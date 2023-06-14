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

bool isNegated(Node n){
  return ((n.getNumChildren()==1 && n.getKind() == kind::NOT)?(!isNegated(n[0])):0);
}

void DratTProofManager::printDratTProof(){
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
      std::cout << "n " << n << std::endl;
      SatLiteral sl = ((n[1] == NodeManager::currentNM()->mkConst(true)) ? cnf.convertAtom(n[0]) : cnf.convertAtom(n[0][0]));
      std::cout << "sl " << sl << std::endl;
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
//      SatLiteral sl = cnf.convertAtom(n);
      SatLiteral sl = ((n[1] == NodeManager::currentNM()->mkConst(true)) ? cnf.convertAtom(n[0]) : cnf.convertAtom(n[0][0]));

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
      std::cout << "(define-fun " << litNode.first.toString() << " () Bool " << litNode.second << ")" << std::endl;
    }
  }
  //Print DIMACS
  //TODO: The literals don't start at 1 which leads to problems with DRAT_trim if p cnf line is not adapted.
  int varNr = ltnm.size() / 2;
  std::cout << "p cnf " << (varNr + 2)<< " " << d_inputClauseNodes.size() << std::endl;
  std::cout << assumptions.str();
  std::cout << lemmas.str();

  //Print DRAT proof
  //TODO: Might need special handling if input is empty
  std::cout << is.rdbuf();
}


//This is similar to LeanPrinter::printSortsAndConstants
void DratTProofManager::printPreamble()
{
  std::cout << "(set-logic ALL)" << std::endl;
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
        std::cout << "(declare-sort " << stc << " " << stc.getUninterpretedSortConstructorArity() << ")" << std::endl;
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
    std::cout << "(declare-fun " << s << " (";
    if(s.getNumChildren() == 0) {
     std::cout << ") " << st << ")" << std::endl;
    }
    else {
      for(auto i = st.begin(), size = st.end()-1; i != size; i++) {
        std::cout << *i << ((i != size - 1)? " " : "");
      }
      std::cout << ") " << *(st.end()-1) << ")" << std::endl;
    }
  }

  

}


} // namespace prop
} // namespace cvc5::internal
