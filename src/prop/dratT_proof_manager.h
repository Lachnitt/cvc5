#include "cvc5_private.h"

#ifndef CVC5__DRATT_PROOF_MANAGER_H
#define CVC5__DRATT_PROOF_MANAGER_H

#include <cvc5/cvc5_types.h>
#include <memory>

#include "context/cdlist.h"
#include "sat_solver_types.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace prop {

class CnfStream;
class ProofCnfStream; //TEMP

class DratTProofManager
{
  public:

  DratTProofManager(std::vector<std::vector<Node>> inputClauseNodes, std::vector<std::vector<Node>> lemmaClauseNodes);
  void printDratTProof();


  private:

  void printPreamble();

  /** Asserted clauses (as node vectors) derived from the input */
  std::vector<std::vector<Node>> d_inputClauseNodes;
  /** Asserted clauses (as node vectors) derived from lemmas */
  std::vector<std::vector<Node>> d_lemmaClauseNodes;

  //Will be replaced by d_cnfStream
  ProofCnfStream* d_pfCnfStream;
  /** The CNF converter in use */
  CnfStream* d_cnfStream;


};
} // namespace prop
} // namespace cvc5::internal

#endif /* CVC5__DRATT_PROOF_MANAGER_H */
