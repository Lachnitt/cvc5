/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Algorithms used by the Alethe post processor
 */

#ifndef CVC5__PROOF__ALETHE__ALETHE_PROOF_PROCESSOR_ALGORITHM_H
#define CVC5__PROOF__ALETHE__ALETHE_PROOF_PROCESSOR_ALGORITHM_H

#include "proof/proof_node_manager.h"

namespace cvc5::internal {

namespace proof {

/** Transforms a term by applying associativity and duplicate removal (using
 * idempotency and commutativity) into its ac normal form without changing the
 * order of a term's already normalized children. Note that in this sense ac is
 * a bit of a misnomer. In contrast to it the CPC rule ACI_NORM where all three
 * properties are used also normalizes identity elements (such as True for the
 * operator and).
 *
 * @param cache A mapping between subterms of the input term and their ac normal
 * form. Should be empty in the beginning.
 * @param term The term that should be transformed.
 * @return The term in ac normal form.
 */
Node applyAcSimp(std::map<Node, Node>& cache, Node term);

/** Transforms a term by removing duplicates and neural elements from its
 * top-level children. It also simplifies the term in case one of its children
 * is the inverse element or two children are the same literal with opposite
 * polarities. Note: This implements Alethe's or_simplify and and_simplify rule.
 * Currently, this does not support Bit-vectors.
 *
 * @param res The term to be simplified
 * @return The simplified term
 */
Node applyNarySimplify(Node res);

}  // namespace proof
}  // namespace cvc5::internal

#endif
