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
 * Base class for sygus enumerators
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS__ENUM_VAL_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS__ENUM_VAL_GENERATOR_H

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

/**
 * A base class for generating values for actively-generated enumerators.
 * At a high level, the job of this class is to accept a stream of "abstract
 * values" a1, ..., an, ..., and generate a (possibly larger) stream of
 * "concrete values" c11, ..., c1{m_1}, ..., cn1, ... cn{m_n}, ....
 */
class EnumValGenerator : protected EnvObj
{
 public:
  EnumValGenerator(Env& env) : EnvObj(env) {}
  virtual ~EnumValGenerator() {}
  /** initialize this class with enumerator e */
  virtual void initialize(Node e) = 0;
  /** Inform this generator that abstract value v was enumerated. */
  virtual void addValue(Node v) = 0;
  /**
   * Increment this value generator. If this returns false, then we are out of
   * values. If this returns true, getCurrent(), if non-null, returns the
   * current term.
   *
   * Notice that increment() may return true and afterwards it may be the case
   * getCurrent() is null. We do this so that increment() does not take too
   * much time per call, which can be the case for grammars where it is
   * difficult to find the next (non-redundant) term. Returning true with
   * a null current term gives the caller the chance to interleave other
   * reasoning.
   */
  virtual bool increment() = 0;
  /** Get the current concrete value generated by this class. */
  virtual Node getCurrent() = 0;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
