#include "prop/dratT_proof_manager.h"

#include "prop/cnf_stream.h"
#include "prop/proof_cnf_stream.h"
#include "prop/sat_solver_types.h"
#include "context/cdlist.h"
#include "expr/node_algorithm.h"
#include "prop/sat_solver_factory.h"
#include "smt/env.h"
#include "prop/sat_proof_manager.h"
#include "prop/cadical.h"

namespace cvc5::internal {
namespace prop {

DratTProofManager::DratTProofManager(std::vector<std::vector<Node>> inputClauseNodes, std::vector<std::vector<Node>> lemmaClauseNodes) : d_inputClauseNodes (inputClauseNodes), d_lemmaClauseNodes (lemmaClauseNodes)
{
  
}

Node removeDoubleNegation(Node n){
  if(n.getKind() != kind::NOT || n.getNumChildren() != 1) {return n;}
  if(n[0].getKind() != kind::NOT) {return n;}
  return n[0][0];
}

void DratTProofManager::printDratTProof(){
  //stream to write to
  std::stringstream out;
  //Print declare-sort and declare-fun
  printPreamble(); 
  //Call Cadical
  Options* opts = new Options();
  Env env(opts);
  StatisticsRegistry sr = StatisticsRegistry(env,true);
  SatSolver* cadical = SatSolverFactory::createCadical(
	sr,
        env.getResourceManager(),
        "DratT",
        true);
	  context::UserContext* userContext = env.getUserContext();
  CnfStream cnf(env,cadical,new NullRegistrar(), userContext, FormulaLitPolicy::TRACK,"dratT");
  //SatProofManager satPM = new SatProofManager(env,static_cast<MinisatSatSolver*>(cadical)->getProofManager,cnf);
  ProofCnfStream pcnf(env, cnf, nullptr);//static_cast<MinisatSatSolver*>(cadical)->getProofManager());
  const context::CDInsertHashMap<SatLiteral, NodeTemplate<false>, SatLiteralHashFunction> &ltnm = cnf.getNodeCache();
  const CnfStream::NodeToLiteralMap &ltnm2 = cnf.getTranslationCache();

  std::stringstream assumptions;
  for (std::vector<Node> icn : d_inputClauseNodes) {
    SatClause cl;
    assumptions << "i ";
    /*if (icn.size() == 1 && icn[0] == NodeManager::currentNM()->mkConst(false)) {
       assumptions << "0" << std::endl;
       cl.push_back(cnf.toCNF(icn[0]));
       cadical->addClause(cl,false);
       break;
     }*/
    for (Node n : icn){
      Node n2 = (n[1] == NodeManager::currentNM()->mkConst(true)) ? n[0] : n[0][0];
      SatLiteral sl;
      if (cnf.hasLiteral(n2)) {
        sl = cnf.getLiteral(n2); }
      else {
        Node n3 = removeDoubleNegation(n2);
        if (cnf.hasLiteral(n3)) {
          sl = cnf.getLiteral(n3); }
        else {
          sl = cnf.convertAtom(n3); }
      }

      cl.push_back(sl);
      if(sl.isNegated()) {
        assumptions << "-" << sl.getSatVariable() << " ";
      }
      else {
        assumptions << sl << " ";
      }
    }
    cadical->addClause(cl,false);
    assumptions << "0" << std::endl;
  }
  std::stringstream lemmas;
  for (std::vector<Node> icn : d_lemmaClauseNodes) {
    SatClause cl;
    lemmas << "t ";
    for (Node n : icn){
      Node n2 = (n[1] == NodeManager::currentNM()->mkConst(true)) ? n[0] : n[0][0];
      SatLiteral sl;
      if (cnf.hasLiteral(n2)) {
        sl = cnf.getLiteral(n2); }
      else {
        Node n3 = removeDoubleNegation(n2);
        if (cnf.hasLiteral(n3)) {
          sl = cnf.getLiteral(n3); }
        else {
          sl = cnf.convertAtom(n3); }
      }


      cl.push_back(sl);
      if(sl.isNegated()) {
        lemmas << "-" << sl.getSatVariable() << " ";
      }
      else {
        lemmas << sl << " ";
      }
    }
    cadical->addClause(cl,false);
    lemmas << "0" << std::endl;
  }

  cadical->solve();
  std::ifstream is = cadical->getDrat();

  //Print mapping
  for (auto litNode : ltnm) {
    if(!litNode.first.isNegated()) {
      out << "(define-fun " << litNode.first.toString() << " () Bool " << litNode.second << ")" << std::endl;
    }
  }
  //Print DIMACS
  //TODO: The literals don't start at 1 which leads to problems with DRAT_trim if p cnf line is not adapted.
  int varNr = ltnm.size() / 2;
  out << "p cnf " << (varNr + 2)<< " " << d_inputClauseNodes.size() << std::endl;
  out << assumptions.str();
  out << lemmas.str();

  //Print DRAT proof
  //TODO: Might need special handling if input is empty
  out << is.rdbuf();
  std::cout << out.rdbuf();
}


//This is similar to LeanPrinter::printSortsAndConstants
std::stringstream DratTProofManager::printPreamble()
{
  std::stringstream out;
  out << "(set-logic ALL)" << std::endl;
  std::unordered_set<Node> syms;
  std::unordered_set<TNode> visited;

  for (const std::vector<Node> n : d_inputClauseNodes)
  {
   for (const Node c: n)
   {
    expr::getSymbols(c[0], syms, visited);
   }
  }

  for (const std::vector<Node> n : d_lemmaClauseNodes)
  {
   for (const Node c: n)
   {
    expr::getSymbols(c[0], syms, visited);
   }
  }

  std::unordered_set<TypeNode> sts;
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    std::unordered_set<TypeNode> ctypes;
    expr::getComponentTypes(st,ctypes);
    for (const TypeNode& stc : ctypes)
    {
      // ignore expression type, should not appear though
      if (stc == nm->sExprType())
      {
        continue;
      }
       // only collect non-predefined sorts for declaration
      if (stc.isUninterpretedSort() && stc.getKind() != kind::TYPE_CONSTANT && sts.find(stc) == sts.end())
      {
        sts.insert(stc);
        //declare new sort
        //TODO: Won't work with assertions on
        out << "(declare-sort " << stc << " " << std::endl; //stc.getUninterpretedSortConstructorArity() << ")" << std::endl;
      }
    }
  }

  //uninterpreted functions
  for (const Node& s :syms)
  {
    TypeNode st = s.getType();
    // ignore symbolic stuff
    if (st == nm->sExprType())
    {
      continue;
    }
    out << "(declare-fun " << s << " (";
    if(s.getNumChildren() == 0) {
     out << ") " << st << ")" << std::endl;
    }
    else {
      for(auto i = st.begin(), size = st.end()-1; i != size; i++) {
        out << *i << ((i != size - 1)? " " : "");
      }
      out << ") " << *(st.end()-1) << ")" << std::endl;
    }
  }
 return out; 

}


} // namespace prop
} // namespace cvc5::internal
