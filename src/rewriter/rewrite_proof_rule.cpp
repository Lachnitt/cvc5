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
 * Rewrite proof rule class
 */

#include "rewriter/rewrite_proof_rule.h"

#include <sstream>

#include "expr/nary_term_util.h"
#include "expr/node_algorithm.h"
#include "proof/proof_checker.h"
#include "rewriter/rewrite_db_sc.h"
#include "rewriter/rewrite_db_term_process.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace rewriter {

bool getDslPfRule(TNode n, DslPfRule& id)
{
  uint32_t i;
  if (ProofRuleChecker::getUInt32(n, i))
  {
    id = static_cast<DslPfRule>(i);
    return true;
  }
  return false;
}

RewriteProofRule::RewriteProofRule()
    : d_id(DslPfRule::FAIL), d_isFixedPoint(false), d_isFlatForm(false)
{
}

void RewriteProofRule::init(DslPfRule id,
                            const std::vector<Node>& userFvs,
                            const std::vector<Node>& fvs,
                            const std::vector<Node>& cond,
                            Node conc,
                            bool isFixedPoint,
                            bool isFlatForm)
{
  // not initialized yet
  Assert(d_cond.empty() && d_obGen.empty() && d_fvs.empty());
  d_id = id;
  d_userFvs = userFvs;
  // Must purify side conditions from the condition. For each subterm of
  // condition c that is an application of a side condition, we replace it
  // with a free variable and add its definition to d_scs. In the end,
  // d_cond contains formulas that have no side conditions, but may have
  // (internally generated) variables.
  for (const Node& c : cond)
  {
    if (!expr::getListVarContext(c, d_listVarCtx))
    {
      Unhandled()
          << "Ambiguous context for list variables in condition of rule " << id;
    }
    d_cond.push_back(c);
    Node cc = purifySideConditions(c, d_scs);
    d_obGen.push_back(cc);
  }
  d_conc = conc;
  d_isFixedPoint = isFixedPoint;
  d_isFlatForm = isFlatForm;
  if (!expr::getListVarContext(conc, d_listVarCtx))
  {
    Unhandled() << "Ambiguous context for list variables in conclusion of rule "
                << id;
  }

  d_numFv = fvs.size();

  std::unordered_set<Node> fvsCond;
  for (const Node& c : d_cond)
  {
    expr::getFreeVariables(c, fvsCond);
  }
  for (const Node& v : fvs)
  {
    d_fvs.push_back(v);
    if (fvsCond.find(v) == fvsCond.end())
    {
      d_noOccVars[v] = true;
    }
  }
  // if fixed point, initialize match utility
  if (d_isFixedPoint)
  {
    d_mt.addTerm(conc[0]);
  }
}

Node RewriteProofRule::purifySideConditions(Node n, std::vector<Node>& scs)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        if (cur.getMetaKind() == metakind::PARAMETERIZED)
        {
          children.insert(children.begin(), cur.getOperator());
        }
        ret = nm->mkNode(cur.getKind(), children);
      }
      if (ret.getKind() == APPLY_UF)
      {
        // Is it a side condition? If so, we replace by a fresh variable
        // and store the defining equality into scs.
        if (RewriteDbSc::isSideCondition(ret.getOperator()))
        {
          std::stringstream ss;
          ss << "k" << (scs.size() + 1);
          Node k = nm->mkBoundVar(ss.str(), cur.getType());
          Node scEq = ret.eqNode(k);
          scs.push_back(scEq);
          ret = k;
        }
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

rewriter::DslPfRule RewriteProofRule::getId() const { return d_id; }

const char* RewriteProofRule::getName() const { return toString(d_id); }

const std::vector<Node>& RewriteProofRule::getUserVarList() const
{
  return d_userFvs;
}
const std::vector<Node>& RewriteProofRule::getVarList() const { return d_fvs; }
bool RewriteProofRule::isExplicitVar(Node v) const
{
  Assert(std::find(d_fvs.begin(), d_fvs.end(), v) != d_fvs.end());
  return d_noOccVars.find(v) != d_noOccVars.end();
}
Kind RewriteProofRule::getListContext(Node v) const
{
  std::map<Node, Kind>::const_iterator it = d_listVarCtx.find(v);
  if (it != d_listVarCtx.end())
  {
    return it->second;
  }
  return UNDEFINED_KIND;
}
bool RewriteProofRule::hasConditions() const { return !d_cond.empty(); }

const std::vector<Node>& RewriteProofRule::getConditions() const
{
  return d_cond;
}

bool RewriteProofRule::hasSideConditions() const { return !d_scs.empty(); }

bool RewriteProofRule::getObligations(const std::vector<Node>& vs,
                                      const std::vector<Node>& ss,
                                      std::vector<Node>& vcs) const
{
  if (!d_scs.empty())
  {
    return runSideConditions(vs, ss, vcs);
  }
  // otherwise, just substitute into each condition
  for (const Node& c : d_obGen)
  {
    Node sc = expr::narySubstitute(c, vs, ss);
    vcs.push_back(sc);
  }
  return true;
}

bool RewriteProofRule::runSideConditions(const std::vector<Node>& vs,
                                         const std::vector<Node>& ss,
                                         std::vector<Node>& vcs) const
{
  // the side condition substitution
  std::vector<Node> vctx = vs;
  std::vector<Node> sctx = ss;
  for (const Node& sc : d_scs)
  {
    Assert(sc.getKind() == kind::EQUAL);
    Node sct = sc[0];
    Assert(sct.getKind() == kind::APPLY_UF);
    Node f = sct.getOperator();
    std::vector<Node> scArgs;
    for (const Node& a : sct)
    {
      Node sa =
          a.substitute(vctx.begin(), vctx.end(), sctx.begin(), sctx.end());
      scArgs.push_back(sa);
    }
    // evaluate the side condition
    Node res = RewriteDbSc::evaluate(f, scArgs);
    if (res.isNull())
    {
      // the side condition failed, return false
      return false;
    }
    // store it in the substitution we are building
    vctx.push_back(sc[1]);
    sctx.push_back(res);
  }
  for (const Node& c : d_obGen)
  {
    Node sc = c.substitute(vctx.begin(), vctx.end(), sctx.begin(), sctx.end());
    vcs.push_back(sc);
  }
  return true;
}

void RewriteProofRule::getMatches(Node h, expr::NotifyMatch* ntm) const
{
  d_mt.getMatches(h, ntm);
}

Node RewriteProofRule::getConclusion() const { return d_conc; }

Node RewriteProofRule::getConclusionFor(const std::vector<Node>& ss) const
{
  Assert(d_fvs.size() == ss.size());
  return expr::narySubstitute(d_conc, d_fvs, ss);
}
bool RewriteProofRule::isFixedPoint() const { return d_isFixedPoint; }
bool RewriteProofRule::isFlatForm() const { return d_isFlatForm; }
}  // namespace rewriter
}  // namespace cvc5
