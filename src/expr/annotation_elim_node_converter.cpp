/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of annotation elimination node conversion
 */

#include "expr/annotation_elim_node_converter.h"

using namespace cvc5::kind;

namespace cvc5 {

AnnotationElimNodeConverter::AnnotationElimNodeConverter() {}

Node AnnotationElimNodeConverter::postConvert(Node n)
{
  if (n.isClosure() && n.getNumChildren() == 3)
  {
    return NodeManager::currentNM()->mkNode(n.getKind(), n[0], n[1]);
  }
  return n;
}

}  // namespace cvc5
