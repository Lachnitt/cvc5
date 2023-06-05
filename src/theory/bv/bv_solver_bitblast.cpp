/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bit-blasting solver that supports multiple SAT backends.
 */

#include "theory/bv/bv_solver_bitblast.h"

#include "options/bv_options.h"
#include "prop/sat_solver_factory.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/**
 * Notifies the BV solver when assertions were reset.
 *
 * This class is notified after every user-context pop and maintains a flag
 * that indicates whether assertions have been reset. If the user-context level
 * reaches level 0 it means that the assertions were reset.
 */
class NotifyResetAssertions : public context::ContextNotifyObj
{
 public:
  NotifyResetAssertions(context::Context* c)
      : context::ContextNotifyObj(c, false),
        d_context(c),
        d_doneResetAssertions(false)
  {
  }

  bool doneResetAssertions() { return d_doneResetAssertions; }

  void reset() { d_doneResetAssertions = false; }

 protected:
  void contextNotifyPop() override
  {
    // If the user-context level reaches 0 it means that reset-assertions was
    // called.
    if (d_context->getLevel() == 0)
    {
      d_doneResetAssertions = true;
    }
  }

 private:
  /** The user-context. */
  context::Context* d_context;

  /** Flag to notify whether reset assertions was called. */
  bool d_doneResetAssertions;
};

/**
 * Bit-blasting registrar.
 *
 * The CnfStream calls preRegister() if it encounters a theory atom.
 * This registrar bit-blasts given atom and remembers which bit-vector atoms
 * were bit-blasted.
 *
 * This registrar is needed when --bitblast=eager is enabled.
 */
class BBRegistrar : public prop::Registrar
{
 public:
  BBRegistrar(NodeBitblaster* bb) : d_bitblaster(bb) {}

  void notifySatLiteral(Node n) override
  {
    if (d_registeredAtoms.find(n) != d_registeredAtoms.end())
    {
      return;
    }
    /* We are only interested in bit-vector atoms. */
    if ((n.getKind() == kind::EQUAL && n[0].getType().isBitVector())
        || n.getKind() == kind::BITVECTOR_ULT
        || n.getKind() == kind::BITVECTOR_ULE
        || n.getKind() == kind::BITVECTOR_SLT
        || n.getKind() == kind::BITVECTOR_SLE)
    {
      d_registeredAtoms.insert(n);
      d_bitblaster->bbAtom(n);
    }
  }

  std::unordered_set<TNode>& getRegisteredAtoms() { return d_registeredAtoms; }

 private:
  /** The bitblaster used. */
  NodeBitblaster* d_bitblaster;

  /** Stores bit-vector atoms encounterd on preRegister(). */
  std::unordered_set<TNode> d_registeredAtoms;
};

BVSolverBitblast::BVSolverBitblast(Env& env,
                                   TheoryState* s,
                                   TheoryInferenceManager& inferMgr)
    : BVSolver(env, *s, inferMgr),
      d_bitblaster(new NodeBitblaster(env, s)),
      d_bbRegistrar(new BBRegistrar(d_bitblaster.get())),
      d_nullContext(new context::Context()),
      d_bbFacts(context()),
      d_bbInputFacts(context()),
      d_assumptions(context()),
      d_assertions(context()),
      d_epg(env.isTheoryProofProducing()
                ? new EagerProofGenerator(env, userContext(), "")
                : nullptr),
      d_factLiteralCache(context()),
      d_literalFactCache(context()),
      d_propagate(options().bv.bitvectorPropagate),
      d_resetNotify(new NotifyResetAssertions(userContext()))
{
  if (env.isTheoryProofProducing())
  {
    d_bvProofChecker.registerTo(env.getProofNodeManager()->getChecker());
    if (d_env.isTheoryProofProducing())
    {
      d_pfBitblaster.reset(new BBProof(d_env, s, false));
    }
  }

  initSatSolver();
}

bool BVSolverBitblast::needsEqualityEngine(EeSetupInfo& esi)
{
  // we always need the equality engine if sharing is enabled for processing
  // equality engine and shared terms
  return logicInfo().isSharingEnabled() || options().bv.bvEqEngine;
}

void BVSolverBitblast::postCheck(Theory::Effort level)
{
  if (level != Theory::Effort::EFFORT_FULL)
  {
    /* Do bit-level propagation only if the SAT solver supports it. */
    if (!d_propagate || !d_satSolver->setPropagateOnly())
    {
      return;
    }
  }

  // If we permanently added assertions to the SAT solver and the assertions
  // were reset, we have to reset the SAT solver and the CNF stream.
  if (options().bv.bvAssertInput && d_resetNotify->doneResetAssertions())
  {
    d_satSolver.reset(nullptr);
    d_cnfStream.reset(nullptr);
    if (d_env.isTheoryProofProducing())
    {
      d_pfCnfStream.reset(nullptr);
    }
    initSatSolver();
    d_resetNotify->reset();
  }

  NodeManager* nm = NodeManager::currentNM();

  /* Process input assertions bit-blast queue. */
  while (!d_bbInputFacts.empty())
  {
    Node fact = d_bbInputFacts.front();
    d_bbInputFacts.pop();
    /* Bit-blast fact and cache literal. */
    if (d_factLiteralCache.find(fact) == d_factLiteralCache.end())
    {
      if (fact.getKind() == kind::BITVECTOR_EAGER_ATOM)
      {
        handleEagerAtom(fact, true);
      }
      else
      {
        handleLazyAtom(fact);
      }
    }
    d_assertions.push_back(fact);
  }

  /* Process bit-blast queue and store SAT literals. */
  while (!d_bbFacts.empty())
  {
    Node fact = d_bbFacts.front();
    d_bbFacts.pop();
    /* Bit-blast fact and cache literal. */
    if (d_factLiteralCache.find(fact) == d_factLiteralCache.end())
    {
      prop::SatLiteral lit;
      if (fact.getKind() == kind::BITVECTOR_EAGER_ATOM)
      {
        handleEagerAtom(fact, false);
        if (d_env.isTheoryProofProducing())
        {
          lit = d_pfCnfStream->getLiteral(fact[0]);
        }
        else
        {
          lit = d_cnfStream->getLiteral(fact[0]);
        }
      }
      else
      {
        Node bb_fact = bitblastAtom(fact);
        if (d_env.isTheoryProofProducing())
        {
          d_pfCnfStream->ensureLiteral(bb_fact);
          lit = d_pfCnfStream->getLiteral(bb_fact);
        }
        else
        {
          d_cnfStream->ensureLiteral(bb_fact);
          lit = d_cnfStream->getLiteral(bb_fact);
        }
      }
      d_factLiteralCache[fact] = lit;
      d_literalFactCache[lit] = fact;
    }
    d_assumptions.push_back(d_factLiteralCache[fact]);
  }

  std::vector<prop::SatLiteral> assumptions(d_assumptions.begin(),
                                            d_assumptions.end());
  prop::SatValue val = d_satSolver->solve(assumptions);

  if (val == prop::SatValue::SAT_VALUE_FALSE)
  {
    std::vector<prop::SatLiteral> unsat_assumptions;
    d_satSolver->getUnsatAssumptions(unsat_assumptions);

    Node conflict;
    // Unsat assumptions produce conflict.
    if (unsat_assumptions.size() > 0)
    {
      std::vector<Node> conf;
      for (const prop::SatLiteral& lit : unsat_assumptions)
      {
        conf.push_back(d_literalFactCache[lit]);
        Trace("bv-bitblast")
            << "unsat assumption (" << lit << "): " << conf.back() << std::endl;
      }
      conflict = nm->mkAnd(conf);
    }
    else  // Input assertions produce conflict.
    {
      std::vector<Node> assertions(d_assertions.begin(), d_assertions.end());
      conflict = nm->mkAnd(assertions);
    }
    raiseConflict(conflict);
  }
}

void BVSolverBitblast::raiseConflict(const Node& conflict)
{
  if (!d_env.isTheoryProofProducing()
      || options().bv.bvSatSolver != options::SatSolverMode::CADICAL)
  {
    d_im.conflict(conflict, InferenceId::BV_BITBLAST_CONFLICT);
    return;
  }
  std::ifstream d_dratProof = d_satSolver->getDrat();
  proof::DratProof dratProof = proof::DratProof::fromPlain(d_dratProof);
  std::vector<Node> dratProofNodes = convertDratProof(dratProof);

  CDProof cdp(d_env, nullptr, "BVSolverBitblast::CDProof", false);
  NodeManager* nm = NodeManager::currentNM();
  TypeNode booleanType = nm->booleanType();
  Node falseResolution = nm->mkConst<bool>(false);

  std::vector<Node> inputClauses = d_pfCnfStream->getInputClauses();
  for (const Node& premise : inputClauses)
  {
    cdp.addProof(d_pfCnfStream->getProofFor(premise));
  }

  std::vector<Node> premises = inputClauses;
  for (const prop::SatLiteral& assumption : d_assumptions)
  {
    premises.emplace_back(d_literalFactCache[assumption]);
  }
  cdp.addStep(falseResolution, PfRule::DRAT_REFUTATION, premises, dratProofNodes);
  cdp.addStep(conflict.notNode(), PfRule::SCOPE, {falseResolution}, premises);

  d_epg->setProofFor(conflict.notNode(), cdp.getProofFor(conflict.notNode()));

  TrustNode trustConflict = TrustNode::mkTrustConflict(conflict, d_epg.get());
  d_im.trustedConflict(trustConflict, InferenceId::BV_BITBLAST_CONFLICT);
}

bool BVSolverBitblast::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Valuation& val = d_state.getValuation();

  /**
   * Check whether `fact` is an input assertion on user-level 0.
   *
   * If this is the case we can assert `fact` to the SAT solver instead of
   * using assumptions.
   */
  if (options().bv.bvAssertInput && val.isFixed(fact))
  {
    Assert(!val.isDecision(fact));
    d_bbInputFacts.push_back(fact);
  }
  else
  {
    d_bbFacts.push_back(fact);
  }
  
  // Return false to enable equality engine reasoning in Theory, which is
  // available if we are using the equality engine.
  return !logicInfo().isSharingEnabled() && !options().bv.bvEqEngine;
}

TrustNode BVSolverBitblast::explain(TNode n)
{
  Trace("bv-bitblast") << "explain called on " << n << std::endl;
  return d_im.explainLit(n);
}

void BVSolverBitblast::computeRelevantTerms(std::set<Node>& termSet)
{
  /* BITVECTOR_EAGER_ATOM wraps input assertions that may also contain
   * equalities. As a result, these equalities are not handled by the equality
   * engine and terms below these equalities do not appear in `termSet`.
   * We need to make sure that we compute model values for all relevant terms
   * in BitblastMode::EAGER and therefore add all variables from the
   * bit-blaster to `termSet`.
   */
  if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  {
    d_bitblaster->computeRelevantTerms(termSet);
  }
}

bool BVSolverBitblast::collectModelValues(TheoryModel* m,
                                          const std::set<Node>& termSet)
{
  for (const auto& term : termSet)
  {
    if ((d_env.isTheoryProofProducing() && !d_pfBitblaster->isVariable(term))
        || !d_bitblaster->isVariable(term))
    {
      continue;
    }

    Node value = getValue(term, true);
    Assert(value.isConst());
    if (!m->assertEquality(term, value, true))
    {
      return false;
    }
  }

  // In eager bitblast mode we also have to collect the model values for
  // Boolean variables in the CNF stream.
  if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<TNode> vars;
    if (d_env.isTheoryProofProducing())
    {
      d_pfCnfStream->getBooleanVariables(vars);
    }
    else
    {
      d_cnfStream->getBooleanVariables(vars);
    }
    for (TNode var : vars)
    {
      prop::SatLiteral bit;
      if (d_env.isTheoryProofProducing())
      {
        Assert(d_pfCnfStream->hasLiteral(var));
        bit = d_pfCnfStream->getLiteral(var);
      }
      else
      {
        Assert(d_cnfStream->hasLiteral(var));
        bit = d_cnfStream->getLiteral(var);
      }
      prop::SatValue value = d_satSolver->value(bit);
      Assert(value != prop::SAT_VALUE_UNKNOWN);
      if (!m->assertEquality(
              var, nm->mkConst(value == prop::SAT_VALUE_TRUE), true))
      {
        return false;
      }
    }
  }

  return true;
}

void BVSolverBitblast::initSatSolver()
{
  switch (options().bv.bvSatSolver)
  {
    case options::SatSolverMode::CRYPTOMINISAT:
      d_satSolver.reset(prop::SatSolverFactory::createCryptoMinisat(
          statisticsRegistry(),
          d_env.getResourceManager(),
          "theory::bv::BVSolverBitblast::"));
      break;
    default:
      d_satSolver.reset(prop::SatSolverFactory::createCadical(
          statisticsRegistry(),
          d_env.getResourceManager(),
          "theory::bv::BVSolverBitblast::",
          d_env.isTheoryProofProducing()));
  }
  d_cnfStream.reset(new prop::CnfStream(
      d_env,
      d_satSolver.get(),
      d_bbRegistrar.get(),
      d_nullContext.get(),
      /**
       * If we are producing proofs for the SAT solver, we need that all
       * literals created in the CNF stream are tracked, which is not the case
       * with FormulaLitPolicy::INTERNAL
       */
      d_env.isTheoryProofProducing() ? prop::FormulaLitPolicy::TRACK
                                     : prop::FormulaLitPolicy::INTERNAL,
      "theory::bv::BVSolverBitblast"));
  if (d_env.isTheoryProofProducing())
  {
    d_pfCnfStream.reset(new prop::ProofCnfStream(
        d_env,
        *d_cnfStream,
        nullptr));
  }
}

Node BVSolverBitblast::getValue(TNode node, bool initialize)
{
  if (node.isConst())
  {
    return node;
  }

  if ((d_env.isTheoryProofProducing() && !d_pfBitblaster->hasBBTerm(node))
      || !d_bitblaster->hasBBTerm(node))
  {
    return initialize ? utils::mkConst(utils::getSize(node), 0u) : Node();
  }

  std::vector<Node> bits;
  if (d_env.isTheoryProofProducing())
  {
    d_pfBitblaster->getBBTerm(node, bits);
  }
  else
  {
    d_bitblaster->getBBTerm(node, bits);
  }
  Integer value(0), one(1), zero(0), bit;
  for (size_t i = 0, size = bits.size(), j = size - 1; i < size; ++i, --j)
  {
    if ((d_env.isTheoryProofProducing() && d_pfCnfStream->hasLiteral(bits[j]))
        || d_cnfStream->hasLiteral(bits[j]))
    {
      prop::SatLiteral lit;
      if (d_env.isTheoryProofProducing())
      {
        lit = d_pfCnfStream->getLiteral(bits[j]);
      }
      else
      {
        lit = d_cnfStream->getLiteral(bits[j]);
      }
      prop::SatValue val = d_satSolver->modelValue(lit);
      bit = val == prop::SatValue::SAT_VALUE_TRUE ? one : zero;
    }
    else
    {
      if (!initialize) return Node();
      bit = zero;
    }
    value = value * 2 + bit;
  }
  return utils::mkConst(bits.size(), value);
}

void BVSolverBitblast::handleEagerAtom(TNode fact, bool assertFact)
{
  Assert(fact.getKind() == kind::BITVECTOR_EAGER_ATOM);

  if (assertFact)
  {
    d_cnfStream->convertAndAssert(fact[0], false, false);
  }
  else
  {
    d_cnfStream->ensureLiteral(fact[0]);
  }

  /* convertAndAssert() does not make the connection between the bit-vector
   * atom and it's bit-blasted form (it only calls preRegister() from the
   * registrar). Thus, we add the equalities now. */
  auto& registeredAtoms = d_bbRegistrar->getRegisteredAtoms();
  for (auto atom : registeredAtoms)
  {
    Node bb_atom = d_bitblaster->getStoredBBAtom(atom);
    d_cnfStream->convertAndAssert(atom.eqNode(bb_atom), false, false);
  }
  // Clear cache since we only need to do this once per bit-blasted atom.
  registeredAtoms.clear();
}

Node BVSolverBitblast::bitblastAtom(TNode fact)
{
  if (d_env.isTheoryProofProducing())
  {
    d_pfBitblaster->bbAtom(fact);
    return d_pfBitblaster->getStoredBBAtom(fact);
  }
  d_bitblaster->bbAtom(fact);
  return d_bitblaster->getStoredBBAtom(fact);
}

void BVSolverBitblast::handleLazyAtom(TNode fact)
{
  Node bb_fact = bitblastAtom(fact);
  if (d_env.isTheoryProofProducing())
  {
    // CHECK THIS CAST
    d_pfCnfStream->convertAndAssert(bb_fact, false, false, true, (ProofGenerator*)d_pfBitblaster->getProofGenerator());
    return;
  }
  d_cnfStream->convertAndAssert(bb_fact, false, false);
}

std::vector<Node> BVSolverBitblast::convertDratProof(
    const proof::DratProof& dratProof) const
{
  NodeManager* nm = NodeManager::currentNM();
  Node cl = nm->mkBoundVar("cl", nm->booleanType());
  Node del = nm->mkBoundVar("del", nm->booleanType());
  Node lastFalseResolution = nm->mkConst<bool>(false);
  prop::SatLiteral zeroLiteral = prop::SatLiteral(0);

  std::vector<Node> args;
  for (const proof::DratInstruction& instruction : dratProof.getInstructions())
  {
    Assert(!instruction.d_clause.empty());
    if (instruction.d_clause[0] == zeroLiteral)
    {
      break;
    }
    std::vector<Node> clauseNodes;
    clauseNodes.emplace_back(
        instruction.d_kind == proof::DratInstructionKind::DELETION ? del : cl);
    for (const prop::SatLiteral& literal : instruction.d_clause)
    {
      if (d_env.isTheoryProofProducing())
      {
        Assert(d_pfCnfStream->hasLiteral(literal));
        clauseNodes.emplace_back(d_pfCnfStream->getNode(literal));
      }
      else
      {
        Assert(d_cnfStream->hasLiteral(literal));
        clauseNodes.emplace_back(d_cnfStream->getNode(literal));
      }
    }
    args.push_back(nm->mkNode(kind::SEXPR, clauseNodes));
  }
  args.push_back(nm->mkNode(kind::SEXPR, {cl, lastFalseResolution}));
  return args;
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
