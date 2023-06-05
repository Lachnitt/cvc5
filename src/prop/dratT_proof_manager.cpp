#include "prop/dratT_proof_manager.h"

#include "prop/cnf_stream.h"
#include "prop/sat_solver_types.h"
#include "context/cdlist.h"
#include "expr/node_algorithm.h"

namespace cvc5::internal {
namespace prop {

DratTProofManager::DratTProofManager(std::vector<std::vector<Node>> inputClauseNodes, std::vector<std::vector<Node>> lemmaClauseNodes) : d_inputClauseNodes (inputClauseNodes), d_lemmaClauseNodes (lemmaClauseNodes)
{
  
}

void DratTProofManager::printDratTProof(){

  //Print preamble: declare-sort and declare-fun
  printPreamble(); 
  std::cout << "Finished preamble" << std::endl;

  //Print mapping
  const context::CDInsertHashMap<SatLiteral, NodeTemplate<false>, SatLiteralHashFunction> &ltnm = d_cnfStream->getNodeCache();

  for (auto litNode : ltnm) {
    if(!litNode.first.isNegated()) {
      std::cout << "(define-fun " << litNode.first.toString() << " " << litNode.second << ")" << std::endl;
    }
  }

  //Print DIMACS
  //std::cout << "p cnf " << ltnm.size() << " " << std::endl;

  //Call Cadical and print DRAT proof 

}


//This is similar to LeanPrinter::printSortsAndConstants
void DratTProofManager::printPreamble()
{
  std::unordered_set<Node> syms;
  std::unordered_set<TNode> visited;

  for (const std::vector<Node> n : d_inputClauseNodes)
  {
std::cout << "n " << n << std::endl;
   for (const Node c: n)
   {
    expr::getSymbols(c, syms, visited);
   }
  }

  for (const std::vector<Node> n : d_lemmaClauseNodes)
  {
   for (const Node c: n)
   {
    expr::getSymbols(c, syms, visited);
   }
  }

  std::unordered_set<TypeNode> sts;
  for (Node s : syms)
  {
    TypeNode st = s.getType();
    if (st.isUninterpretedSort() && sts.find(st) == sts.end())
    {
      //declare new sort
      sts.insert(st);
      std::cout << "(declare-sort " << st << " " << st.getUninterpretedSortConstructorArity() << ")" << std::endl;
    }
    std::cout << "(declare-fun " << s << " " << "() " << st << ")" << std::endl;
  }

}


} // namespace prop
} // namespace cvc5::internal
