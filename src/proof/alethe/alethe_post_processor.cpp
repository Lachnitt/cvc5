/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing proof nodes into Alethe proof nodes
 */

#include "proof/alethe/alethe_post_processor.h"

#include <sstream>

#include "expr/nary_term_util.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "proof/alethe/alethe_post_processor_algorithm.h"
#include "proof/alethe/alethe_proof_rule.h"
#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "proof/resolution_proofs_util.h"
#include "rewriter/rewrite_proof_rule.h"
#include "smt/env.h"
#include "theory/arith/arith_poly_norm.h"
#include "theory/builtin/proof_checker.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

namespace proof {

std::unordered_map<Kind, AletheRule> s_bvKindToAletheRule = {
    {Kind::BITVECTOR_COMP, AletheRule::BV_BITBLAST_STEP_BVCOMP},
    {Kind::BITVECTOR_ULT, AletheRule::BV_BITBLAST_STEP_BVULT},
    {Kind::BITVECTOR_ULE, AletheRule::BV_BITBLAST_STEP_BVULE},
    {Kind::BITVECTOR_SLT, AletheRule::BV_BITBLAST_STEP_BVSLT},
    {Kind::BITVECTOR_AND, AletheRule::BV_BITBLAST_STEP_BVAND},
    {Kind::BITVECTOR_OR, AletheRule::BV_BITBLAST_STEP_BVOR},
    {Kind::BITVECTOR_XOR, AletheRule::BV_BITBLAST_STEP_BVXOR},
    {Kind::BITVECTOR_XNOR, AletheRule::BV_BITBLAST_STEP_BVXNOR},
    {Kind::BITVECTOR_NOT, AletheRule::BV_BITBLAST_STEP_BVNOT},
    {Kind::BITVECTOR_ADD, AletheRule::BV_BITBLAST_STEP_BVADD},
    {Kind::BITVECTOR_NEG, AletheRule::BV_BITBLAST_STEP_BVNEG},
    {Kind::BITVECTOR_MULT, AletheRule::BV_BITBLAST_STEP_BVMULT},
    {Kind::BITVECTOR_CONCAT, AletheRule::BV_BITBLAST_STEP_CONCAT},
    {Kind::CONST_BITVECTOR, AletheRule::BV_BITBLAST_STEP_CONST},
    {Kind::BITVECTOR_EXTRACT, AletheRule::BV_BITBLAST_STEP_EXTRACT},
    {Kind::BITVECTOR_SIGN_EXTEND, AletheRule::BV_BITBLAST_STEP_SIGN_EXTEND},
    {Kind::EQUAL, AletheRule::BV_BITBLAST_STEP_BVEQUAL},
};

AletheProofPostprocessCallback::AletheProofPostprocessCallback(
    Env& env, AletheNodeConverter& anc, bool resPivots)
    : EnvObj(env), d_anc(anc), d_resPivots(resPivots)
{
  NodeManager* nm = nodeManager();
  d_cl = nm->mkBoundVar("cl", nm->sExprType());
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

const std::string& AletheProofPostprocessCallback::getError()
{
  return d_reasonForConversionFailure;
}

bool AletheProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                  const std::vector<Node>& fa,
                                                  bool& continueUpdate)
{
  return d_reasonForConversionFailure.empty()
         && pn->getRule() != ProofRule::ALETHE_RULE;
}

bool AletheProofPostprocessCallback::shouldUpdatePost(
    std::shared_ptr<ProofNode> pn, const std::vector<Node>& fa)
{
  if (!d_reasonForConversionFailure.empty() || pn->getArguments().empty())
  {
    return false;
  }
  AletheRule rule = getAletheRule(pn->getArguments()[0]);
  return rule == AletheRule::RESOLUTION_OR || rule == AletheRule::REORDERING
         || rule == AletheRule::CONTRACTION;
}

Node AletheProofPostprocessCallback::mkNodeFromPolyNorm(theory::arith::PolyNorm ret)
{
  NodeManager* nm = NodeManager::currentNM();
  if (ret.empty()) {return nm->mkConstReal(0);}
  std::vector<Node> children;
  for(const auto& elem : ret.d_polyNorm){
     if (elem.first == TNode::null()) {continue;}
     children.push_back(nm->mkNode(Kind::MULT,elem.first, nm->mkConstReal(elem.second)));
  }
  return nm->mkNode(Kind::ADD,children); 
}

// TODO: Re-add bit-vector handling
// Polynomials are normalized by normalizing all subterms and then merging them
// back together in a way that yields a normalized polynomial. Therefore we aim
// to have proofs of terms (= x N(x)) where N is the normalization function for
// all subterms. We rely on the inductive hypothesis that for (k t1 ... tn) we
// have already added proofs for N(t1) ... N(tn) which allows us to add a proof
// for N(k t1 ... tn)
theory::arith::PolyNorm AletheProofPostprocessCallback::mkPolyNorm(TNode n, const TypeNode &arith_type, CDProof* cdp)
{
  NodeManager* nm = NodeManager::currentNM();
  Rational one(1);
  Node null;
  std::unordered_map<TNode, theory::arith::PolyNorm> visited;
  std::unordered_map<TNode, theory::arith::PolyNorm>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  TypeNode arith_t = n.getType();
  bool success = true;
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    Kind k = cur.getKind();
    // During the first phase, proofs of reflexivity are added for constants and
    // leaf nodes since for those it holds that N(c) = c. For example, (= 1 1),
    // (= 5.2 5.2) or (= x3 x3).
    if (it == visited.end())
    {
      if (k == Kind::CONST_RATIONAL || k == Kind::CONST_INTEGER)
      {
        Rational r = cur.getConst<Rational>();
        visited[cur].addMonomial(null, r);
        visit.pop_back();

        // Add proof for positive constants
        Node const_real = nm->mkConstRealOrInt(r);
        Node refl_step = nm->mkNode(Kind::EQUAL,const_real,const_real);
	success &= addAletheStep(AletheRule::REFL,
                         refl_step,
                         nm->mkNode(Kind::SEXPR, d_cl, refl_step),
                         {},
                         {},
                         *cdp);

        continue;
      }
      else if (k == Kind::ADD || k == Kind::SUB || k == Kind::NEG
               || k == Kind::MULT || k == Kind::NONLINEAR_MULT
               || k == Kind::TO_REAL)
      {
        visited[cur] = theory::arith::PolyNorm();
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }

        // Add proof for negative constants
        // Should not be needed, try to delete in the end
        if ((k == Kind::SUB && cur.getNumChildren() == 1) || k == Kind::NEG){
          Kind c_kind = cur[0].getKind();
          if (c_kind == Kind::CONST_RATIONAL || c_kind == Kind::CONST_INTEGER)
          {
            Node r = nm->mkNode(
                k, nm->mkConstRealOrInt(cur[0].getConst<Rational>()));
            Node refl_step = nm->mkNode(Kind::EQUAL, r, r);
            success &= addAletheStep(AletheRule::REFL,
                                     refl_step,
                                     nm->mkNode(Kind::SEXPR, d_cl, refl_step),
                                     {},
                                     {},
                                     *cdp);
          }
        }
	
        continue;
      }
      else if (k == Kind::DIVISION || k == Kind::DIVISION_TOTAL)
     {
        // only division by non-zero constant is supported
        if (cur[1].isConst() && cur[1].getConst<Rational>().sgn() != 0)
        {
          visited[cur] = theory::arith::PolyNorm();
          visit.push_back(cur[0]);

          // Add proof for constant division
          // Should not be needed, try to delete in the end
          Node refl_step = nm->mkNode(Kind::EQUAL, cur[0], cur[0]);
          success &= addAletheStep(AletheRule::REFL,
                                   refl_step,
                                   nm->mkNode(Kind::SEXPR, d_cl, refl_step),
                                   {},
                                   {},
                                   *cdp);

          continue;
        }
      }
      // it is a leaf
      visited[cur].addMonomial(cur, one);

      // Add proof for atoms (variables, constants, terms with other operators
      // then the aboves)
      Node refl_step = nm->mkNode(Kind::EQUAL, cur, cur);
      success &= addAletheStep(AletheRule::REFL,
                         refl_step,
                         nm->mkNode(Kind::SEXPR, d_cl, refl_step),
                         {},
                         {},
                         *cdp);

      continue;
    }
    visit.pop_back();
    // In the second phase we add proofs for composite terms that use one of the
    // supported operators
    Trace("alethe-proof") << "current node : " << cur << " with type "
                          << cur.getType() << std::endl;
    Trace("alethe-proof") << push;
    if (it->second.empty())
    {
      theory::arith::PolyNorm& ret = visited[cur];
      std::stringstream out;
      switch (k)
      {
        case Kind::ADD:
        case Kind::SUB:
        case Kind::NEG:
        case Kind::MULT:
        case Kind::NONLINEAR_MULT:
        case Kind::TO_REAL:
	{
          // The proofs are added later but we collect information about the
          // steps could be minimized
          std::vector<Node> cumulative_normalized;
          std::vector<Node> to_be_added;

          for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
          {
            it = visited.find(cur[i]);
            Assert(it != visited.end());

            // Proofs
            Trace("alethe-proof")
                << "current child : " << cur[i] << " with type "
                << cur[i].getType() << std::endl;
            // polynom q to be added/subtracted/multiplied to p
            Node cur_polynom =
                it->second.theory::arith::PolyNorm::toNode(cur[i].getType());
            Trace("alethe-proof")
                << "current polynom " << cur_polynom << " with type "
                << cur_polynom.getType() << std::endl;

            if ((k == Kind::SUB && i == 1) || k == Kind::NEG)
            {
              ret.subtract(it->second);
            }
            else if (i > 0
                     && (k == Kind::MULT || k == Kind::NONLINEAR_MULT))
            {
              ret.multiply(it->second);
            }
            // I had to add this for proofs
            else if (k == Kind::TO_REAL)
            {
              ret.to_real(it->second);
            }
            else
            {
              ret.add(it->second);
            }

	    // Proof
            TypeNode arith_t3 = (k == Kind::TO_REAL)
                                    ? nm->realType()
                                    : cur[i].getType();  // TODO
            Node new_polynom = ret.theory::arith::PolyNorm::toNode(arith_t3);
            Trace("alethe-proof")
                << "  new polynom " << new_polynom << "with type "
                << new_polynom.getType() << std::endl;
            cumulative_normalized.push_back(new_polynom);
            to_be_added.push_back(cur_polynom);
          }
	  std::vector<Node> ris = {};
          if (k == Kind::TO_REAL
              || (k == Kind::SUB && cur.getNumChildren() == 1)
              || k == Kind::NEG)
          {
            Node ti = nm->mkNode(k, cur[0]);
            Node vp1 = nm->mkNode(Kind::EQUAL, ti, cumulative_normalized[0]);
            Node prems = nm->mkNode(Kind::EQUAL, cur[0], to_be_added[0]);
            success &= addAletheStep(AletheRule::RARE_REWRITE,
                           vp1,
                           nm->mkNode(Kind::SEXPR, d_cl, vp1),
                           {},
                           {nm->mkRawSymbol("\"evaluate\"", nm->sExprType())},
                           *cdp);

          }
          else
          {  // The original form is cur = (k r_1 ... r_n)

            // For each i:
            //   Let t_i = (k r_1 ... r_i) and p_i be the normalized form of
            //   t_i. Let n_i be the normalized form of r_

            // In round i:
            //   n_i gets merged to p_{i-1}, creating p_i
            //   vp1           (= t_{i-1} p_{i-1})           already proven
            //   vp2           (= r_i n_i)                   already proven

            // I want a proof for (= t_i p_i)

            // For i = 0
            // (= t_0 p_0) because t0 = r0 and p_0 = n0 the goal is (= r_0 n_0)
            // which should be already proven

            // Let u_i = (k t_{i-1} r_i) and v_i =  (k p_{i-1} n_i)
            // vp3   (= u_i t_i)   by hole
            // vp4   (= t_i u_i)   by symm vp3
            // vp5   (= u_i v_i)   by cong k with vp1 vp2 
	    // vp6   (= t_i v_i)   by trans with vp4 vp5 
	    // vp7   (= v_i pi)    by
            // k_proof_simplify vp8                (= t_i p_i) by trans vp6 vp7

            for (int i = 0; i < cur.getNumChildren(); i++)
            {
              ris.push_back(cur[i]);
              if (i != 0)
              {
                Trace("alethe-proof") << "... in i not 1" << k << " \n";
                Node ti = nm->mkNode(k, ris);
                std::vector<Node> old_ris;
                old_ris.insert(old_ris.end(), ris.begin(), ris.end() - 1);
                Node timinus1 =
                    (i == 1
                     && cvc5::internal::kind::metakind::getMinArityForKind(k)
                            > 1)
                        ? old_ris[0]
                        : nm->mkNode(k, old_ris);
                Node ni = to_be_added[i];
                Node niminus1 = to_be_added[i - 1];
                Node ri = cur[i];
                Node riminus1 = cur[i - 1];
                Node pi = cumulative_normalized[i];
                Node piminus1 = cumulative_normalized[i - 1];

                Node vp1 = nm->mkNode(Kind::EQUAL, timinus1, piminus1);
                Node vp2 = nm->mkNode(Kind::EQUAL, ri, ni);
                // std::cout << "vp1 " << vp1 << " " << vp1.getType() <<
                // std::endl; std::cout << "vp2 " << vp2 << " " << vp2.getType()
                // << std::endl;

                Node ui = nm->mkNode(k, timinus1, ri);
                Node vi = nm->mkNode(k, piminus1, ni);
                Node vp3 = nm->mkNode(Kind::EQUAL, ui, ti);
                bool vp3_refl = (ui == ti);
                Node vp4 = nm->mkNode(Kind::EQUAL, ti, ui);
                bool vp4_refl = (ti == ui);
                Node vp5 = nm->mkNode(Kind::EQUAL, ui, vi);
                bool vp5_refl = (vi == ui);
                Node vp6 = nm->mkNode(Kind::EQUAL, ti, vi);
                bool vp6_refl = (vi == ti);
                Node vp7 = nm->mkNode(Kind::EQUAL, vi, pi);
                bool vp7_refl = (vi == pi);
                Node vp8 = nm->mkNode(Kind::EQUAL, ti, pi);
                bool vp8_refl = (ti == pi);

                if (vp8_refl)
                {
                  success &= addAletheStep(AletheRule::REFL,
                                           vp8,
                                           nm->mkNode(Kind::SEXPR, d_cl, vp8),
                                           {},
                                           {},
                                           *cdp);
                }
                else
                {
                  if (vp6_refl)
                  {
                    success &= addAletheStep(AletheRule::REFL,
                                             vp6,
                                             nm->mkNode(Kind::SEXPR, d_cl, vp6),
                                             {},
                                             {},
                                             *cdp);
                  }
                  else
                  {
                    if (vp4_refl)
                    {
                      success &=
                          addAletheStep(AletheRule::REFL,
                                        vp4,
                                        nm->mkNode(Kind::SEXPR, d_cl, vp4),
                                        {},
                                        {},
                                        *cdp);
                    }
                    else
                    {
                      if (vp3_refl)
                      {
                        success &=
                            addAletheStep(AletheRule::REFL,
                                          vp3,
                                          nm->mkNode(Kind::SEXPR, d_cl, vp3),
                                          {},
                                          {},
                                          *cdp);
                      }
                      else
                      {
                        Trace("alethe-proof") << "... 00100000" << " \n";
                        success &=
                            addAletheStep(AletheRule::HOLE,
                                          vp3,
                                          nm->mkNode(Kind::SEXPR, d_cl, vp3),
                                          {},
                                          {},
                                          *cdp);
                      }

                      success &=
                          addAletheStep(AletheRule::SYMM,
                                        vp4,
                                        nm->mkNode(Kind::SEXPR, d_cl, vp4),
                                        {vp3},
                                        {},
                                        *cdp);
                    }
                    success &=
                        addAletheStep(AletheRule::CONG,
                                      vp5,
                                      nm->mkNode(Kind::SEXPR, d_cl, vp5),
                                      {vp1, vp2},
                                      {},
                                      *cdp)
                        && addAletheStep(AletheRule::TRANS,
                                         vp6,
                                         nm->mkNode(Kind::SEXPR, d_cl, vp6),
                                         {vp4, vp5},
                                         {},
                                         *cdp);
                  }
                  if (vp7_refl)
                  {
                    success &= addAletheStep(AletheRule::REFL,
                                             vp7,
                                             nm->mkNode(Kind::SEXPR, d_cl, vp7),
                                             {},
                                             {},
                                             *cdp);
                  }
                  else
                  {
                    Trace("alethe-proof") << "... 0000000" << " \n";
                    success &= addAletheStep(AletheRule::HOLE,
                                             vp7,
                                             nm->mkNode(Kind::SEXPR, d_cl, vp7),
                                             {},
                                             {},
                                             *cdp);
                  }
                  success &= addAletheStep(AletheRule::TRANS,
                                           vp8,
                                           nm->mkNode(Kind::SEXPR, d_cl, vp8),
                                           {vp6, vp7},
                                           {},
                                           *cdp);

                  Trace("alethe-proof")
                      << "... mkPolyNorm finished proof that " << vp8 << " \n";
                }
              }
            }
          }
          break;
	}
        case Kind::DIVISION:
        case Kind::DIVISION_TOTAL:
        {
          it = visited.find(cur[0]);
          Assert(it != visited.end());
          ret.add(it->second);
          Assert(cur[1].isConst());
          // multiply by inverse
          Rational invc = cur[1].getConst<Rational>().inverse();
          ret.multiplyMonomial(TNode::null(), invc);
        }
        break;
        case Kind::CONST_RATIONAL:
        case Kind::CONST_INTEGER:
          // ignore, this is the case of a repeated zero, since we check for
          // empty of the polynomial above.
          break;
        default: Unhandled() << "Unhandled polynomial operation " << cur; break;
      }
    }
    Trace("alethe-proof") << pop;
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());

  TypeNode arith_t3 = n.getType();
  // std::cout << "n " << n << " type " << n.getType() << std::endl;;
  Trace("alethe-proof") << "... mkPolyNorm normalized form of " << n << " is "
                        << visited[n].theory::arith::PolyNorm::toNode(arith_t3)
                        << "\n";
  return visited[n];
}

bool AletheProofPostprocessCallback::updateTheoryRewriteProofRewriteRule(
    Node res,
    ProofRule id,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp,
    bool& continueUpdate,
    ProofRewriteRule di)
{
  NodeManager* nm = nodeManager();
  std::vector<Node> new_args = std::vector<Node>();
  switch (di)
  {
    // ======== DISTINCT_ELIM
    // This rule is translated according to the clauses pattern. The only
    // exception to this is if there are more than two terms that are distinct
    // and they are boolean. The Alethe distinct_elim rule has a special
    // handling in these cases and rewrites the distinct term to False directly
    // (as the DISTINCT_CARD_CONFLICT rule does in cvc5).
    case ProofRewriteRule::DISTINCT_ELIM:
    {
      Assert(res.getNumChildren() == 2);
      Assert(res[0].getNumChildren() >= 2);
      if (res[0][0].getType().isBoolean() && res[0].getNumChildren() == 2)
      {
        break;
      }
      return addAletheStep(AletheRule::DISTINCT_ELIM,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           new_args,
                           *cdp);
      break;
    }
    // ======== DISTINCT_CARD_CONFLICT
    // This rule is translated according to the clauses pattern.
    case ProofRewriteRule::DISTINCT_CARD_CONFLICT:
    {
      return addAletheStep(AletheRule::DISTINCT_ELIM,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           new_args,
                           *cdp);
    }
    case ProofRewriteRule::ARITH_DIV_BY_CONST_ELIM:
    {
      Assert(res.getNumChildren() == 2);
      Assert(res[0].getNumChildren() == 2);

      Node rule = nm->mkRawSymbol("\"arith-div-by-const-elim\"", nm->sExprType());
      new_args.push_back(rule);
      new_args.push_back(res[0][0]);
      new_args.push_back(res[0][1]);
      return addAletheStep(AletheRule::RARE_REWRITE,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           {},
                           new_args,
                           *cdp);
    }
    case ProofRewriteRule::EXISTS_ELIM:
    {
    // (exists (x1 ... xn) F) = (not (forall (x1 ... xn) (not F)))
      Assert(res.getNumChildren() == 2);
      Assert(res[0].getNumChildren() == 2);
      // vp1: (= (forall (x1 ... xn) (not F)) (not (exists (x1 ... xn) (not (not F)))) //connective_def
      // vp2: (not (exists (x1 .. xn) (not (not F)))) = (not (exists (x1 ... xn) F))   // rare rewrite 

     // vp4: (= (forall (x1 ... xn) (not F)) (not (exists (x1 ... xn) F)) //trans
     // vp5: (= (not (forall (x1 ... xn) (not F))) (not (not (exists (x1 ... xn) F))) //cong
     // vp6: (= (not (not (exists (x1 ... xn) F))) (exists (x1 .. xn) F) //not_simplify 
     // vp7: (= (not (forall (x1 ... xn) (not F))) (exists (x1 ... xn) F)) //trans
     
      Node exists_F = res[0];
      Node not_forall_not_F = res[1];
      Node variable_list = exists_F[0];
      Node F = exists_F[1];
      Node not_F = F.notNode();
      Node not_not_F = not_F.notNode();
      Node exists_not_not_F = nm->mkNode(Kind::EXISTS,variable_list,not_not_F);
      Node forall_not_F = not_forall_not_F[0];
      Node vp1 = nm->mkNode(Kind::EQUAL, forall_not_F, exists_not_not_F.notNode());
      Node vp2 = nm->mkNode(Kind::EQUAL, exists_not_not_F.notNode(), exists_F.notNode());
      Node vp4 = nm->mkNode(Kind::EQUAL, forall_not_F, exists_F.notNode());

      Node vp5 = nm->mkNode(Kind::EQUAL, forall_not_F.notNode(), exists_F.notNode().notNode());
      Node vp6 = nm->mkNode(Kind::EQUAL, exists_F.notNode().notNode(), exists_F);
      Node vp7 = nm->mkNode(Kind::EQUAL, forall_not_F.notNode(), exists_F);

      return
	addAletheStep(AletheRule::CONNECTIVE_DEF,
                           vp1,
                           nm->mkNode(Kind::SEXPR, d_cl, vp1),
                           {},
                           {},
                           *cdp)
        &&
        addAletheStep(AletheRule::RARE_REWRITE,
                           vp2,
                           nm->mkNode(Kind::SEXPR, d_cl, vp2),
                           {},
                           {},
                           *cdp)
        && addAletheStep(AletheRule::TRANS,
                           vp4,
                           nm->mkNode(Kind::SEXPR, d_cl, vp4),
                           {vp1,vp2},
                           {},
                           *cdp)
        && addAletheStep(AletheRule::CONG,
                           vp5,
                           nm->mkNode(Kind::SEXPR, d_cl, vp5),
                           {vp4},
                           {},
                           *cdp)
        && addAletheStep(AletheRule::NOT_SIMPLIFY,
                           vp6,
                           nm->mkNode(Kind::SEXPR, d_cl, vp6),
                           {},
                           {},
                           *cdp)
        && addAletheStep(AletheRule::TRANS,
                           vp7,
                           nm->mkNode(Kind::SEXPR, d_cl, vp7),
                           {vp5,vp6},
                           {},
                           *cdp)
	&& addAletheStep(AletheRule::SYMM,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           {vp7},
                           {},
                           *cdp);



    }
    default: break;
  }
  return addAletheStep(AletheRule::HOLE,
                       res,
                       nm->mkNode(Kind::SEXPR, d_cl, res),
                       children,
                       new_args,
                       *cdp);
}

bool AletheProofPostprocessCallback::update(Node res,
                                            ProofRule id,
                                            const std::vector<Node>& children,
                                            const std::vector<Node>& args,
                                            CDProof* cdp,
                                            bool& continueUpdate)
{
  Trace("alethe-proof") << "...Alethe pre-update " << res << " " << id << " "
                        << children << " / " << args << std::endl;

  NodeManager* nm = nodeManager();
  std::vector<Node> new_args = std::vector<Node>();

  switch (id)
  {
    // To keep the original shape of the proof node it is necessary to rederive
    // the original conclusion. However, the term that should be printed might
    // be different from that conclusion. Thus, it is stored as an additional
    // argument in the proof node. Usually, the only difference is an additional
    // cl operator or the outmost or operator being replaced by a cl operator.
    //
    // When steps are added to the proof that have not been there previously,
    // it is unwise to add them in the same manner. To illustrate this the
    // following counterexample shows the pitfalls of this approach:
    //
    //  (or a (or b c))   (not a)
    // --------------------------- RESOLUTION
    //  (or b c)
    //
    //  is converted into an Alethe proof that should be printed as
    //
    //  (cl a (or b c))   (cl (not a))
    // -------------------------------- RESOLUTION
    //  (cl (or b c))
    // --------------- OR
    //  (cl b c)
    //
    // Here, (cl (or b c)) and (cl b c) cannot correspond to the same proof node
    // (or b c). Thus, we build a new proof node using the kind SEXPR
    // that is then printed as (cl (or b c)).
    //
    // Adding an OR node to a premises will take place in the finalize function
    // where in the case that a step is printed as (cl (or F1 ... Fn)) but used
    // as (cl F1 ... Fn) an OR step is added to transform it to this very thing.
    // This is necessary for rules that work on clauses, i.e. RESOLUTION,
    // CHAIN_RESOLUTION, REORDERING and FACTORING.
    //
    // Some proof rules have a close correspondence in Alethe. There are two
    // very frequent patterns that, to avoid repetition, are described here and
    // referred to in the comments on the specific proof rules below.
    //
    // The first pattern, which will be called singleton pattern in the
    // following, adds the original proof node F with the corresponding rule R'
    // of the Alethe calculus and uses the same premises as the original proof
    // node (P1:F1) ... (Pn:Fn). However, the conclusion is printed as (cl F).
    //
    // This means a cvc5 rule R that looks as follows:
    //
    //  (P1:F1) ... (Pn:Fn)
    // --------------------- R
    //  F
    //
    // is transformed into:
    //
    //  (P1:F1) ... (Pn:Fn)
    // --------------------- R'
    //  (cl F)*
    //
    // * the corresponding proof node is F
    //
    // The second pattern, which will be called clause pattern in the following,
    // has a disjunction (or G1 ... Gn) as conclusion. It also adds the orignal
    // proof node (or G1 ... Gn) with the corresponding rule R' of the Alethe
    // calculus and uses the same premises as the original proof node (P1:F1)
    // ... (Pn:Fn). However, the conclusion is printed as (cl G1 ... Gn), i.e.
    // the or is replaced by the cl operator.
    //
    // This means a cvc5 rule R that looks as follows:
    //
    //  (P1:F1) ... (Pn:Fn)
    // --------------------- R
    //  (or G1 ... Gn)
    //
    // Is transformed into:
    //
    //  (P1:F1) ... (Pn:Fn)
    // --------------------- R'
    //  (cl G1 ... Gn)*
    //
    // * the corresponding proof node is (or G1 ... Gn)
    //
    // The documentation for each translation below will use variable names as
    // defined in the original documentation of the rules in proof_rule.h.
    //================================================= Core rules
    //======================== Assume and Scope
    // nothing happens
    case ProofRule::ASSUME:
    {
      return false;
    }
    // The SCOPE rule is translated into Alethe using the "subproof" rule. The
    // conclusion is either (=> (and F1 ... Fn) F) or (not (and F1 ... Fn)), so
    // it must be converted into (cl (not F1) ... (not Fn) F), and extra steps
    // must be added to derive the original conclusion, which is the one to be
    // used in the steps depending on this one.
    //
    // The following transformation is applied. Let (not (and F1 ... Fn))^i
    // denote the repetition of (not (and F1 ...  Fn)) for i times.
    //
    // T1:
    //
    // -------------------------------- anchor
    // ---- assume         ---- assume
    //  F1            ...   Fn
    //        ...
    // -----
    //   F
    // ----- subproof    ------- ... ------- and_pos
    //  VP1               VP2_1  ...  VP2_n
    // ------------------------------------ resolution
    //               VP2a
    // ------------------------------------ reordering
    //  VP2b
    // ------ contraction           ------- implies_neg1
    //   VP3                          VP4
    // ------------------------------------ resolution    ------- implies_neg2
    //    VP5                                                VP6
    // ----------------------------------------------------------- resolution
    //                               VP7
    //
    // VP1: (cl (not F1) ... (not Fn) F)
    // VP2_i: (cl (not (and F1 ... Fn)) Fi), for i = 1 to n
    // VP2a: (cl F (not (and F1 ... Fn))^n)
    // VP2b: (cl (not (and F1 ... Fn))^n F)
    // VP3: (cl (not (and F1 ... Fn)) F)
    // VP4: (cl (=> (and F1 ... Fn) F) (and F1 ... Fn)))
    // VP5: (cl (=> (and F1 ... Fn) F) F)
    // VP6: (cl (=> (and F1 ... Fn) F) (not F))
    // VP7: (cl (=> (and F1 ... Fn) F) (=> (and F1 ... Fn) F))
    //
    // Note that if n = 1, then the "subproof" step yields (cl (not F1) F),
    // which is the same as VP3. Since VP1 = VP3, the steps for that
    // transformation are not generated.
    //
    //
    // If F = false:
    //
    //                                    --------- implies_simplify
    //    T1                                 VP9
    // --------- contraction              --------- equiv_1
    //    VP8                                VP10
    // -------------------------------------------- resolution
    //          (cl (not (and F1 ... Fn)))*
    //
    // VP8: (cl (=> (and F1 ... Fn) false))
    // VP9: (cl (= (=> (and F1 ... Fn) false) (not (and F1 ... Fn))))
    // VP10: (cl (not (=> (and F1 ... Fn) false)) (not (and F1 ... Fn)))
    //
    // Otherwise,
    //                T1
    //  ------------------------------ contraction
    //   (cl (=> (and F1 ... Fn) F))**
    //
    //
    // *  the corresponding proof node is (not (and F1 ... Fn))
    // ** the corresponding proof node is (=> (and F1 ... Fn) F)
    case ProofRule::SCOPE:
    {
      bool success = true;

      // Build vp1
      std::vector<Node> negNode{d_cl};
      for (const Node& arg : args)
      {
        negNode.push_back(arg.notNode());  // (not F1) ... (not Fn)
      }
      negNode.push_back(children[0]);  // (cl (not F1) ... (not Fn) F)
      Node vp1 = nm->mkNode(Kind::SEXPR, negNode);
      success &= addAletheStep(
          AletheRule::ANCHOR_SUBPROOF, vp1, vp1, children, args, *cdp);

      Node andNode, vp3;
      if (args.size() == 1)
      {
        vp3 = vp1;
        andNode = args[0];  // F1
      }
      else
      {
        // Build vp2i
        andNode = nm->mkNode(Kind::AND, args);  // (and F1 ... Fn)
        std::vector<Node> premisesVP2 = {vp1};
        std::vector<Node> notAnd = {d_cl, children[0]};  // cl F
        Node vp2_i;
        for (size_t i = 0, size = args.size(); i < size; i++)
        {
          vp2_i = nm->mkNode(Kind::SEXPR, d_cl, andNode.notNode(), args[i]);
          success &= addAletheStep(AletheRule::AND_POS,
                                   vp2_i,
                                   vp2_i,
                                   {},
                                   std::vector<Node>{nm->mkConstInt(i)},
                                   *cdp);
          premisesVP2.push_back(vp2_i);
          notAnd.push_back(andNode.notNode());  // cl F (not (and F1 ... Fn))^i
        }

        Node vp2a = nm->mkNode(Kind::SEXPR, notAnd);
        if (d_resPivots)
        {
          std::vector<Node> newArgs;
          for (const Node& arg : args)
          {
            newArgs.push_back(arg);
            newArgs.push_back(d_false);
          }
          success &= addAletheStep(
              AletheRule::RESOLUTION, vp2a, vp2a, premisesVP2, newArgs, *cdp);
        }
        else
        {
          success &= addAletheStep(AletheRule::RESOLUTION,
                                   vp2a,
                                   vp2a,
                                   premisesVP2,
                                   std::vector<Node>(),
                                   *cdp);
        }

        notAnd.erase(notAnd.begin() + 1);  //(cl (not (and F1 ... Fn))^n)
        notAnd.push_back(children[0]);     //(cl (not (and F1 ... Fn))^n F)
        Node vp2b = nm->mkNode(Kind::SEXPR, notAnd);
        success &=
            addAletheStep(AletheRule::REORDERING, vp2b, vp2b, {vp2a}, {}, *cdp);

        vp3 = nm->mkNode(Kind::SEXPR, d_cl, andNode.notNode(), children[0]);
        success &=
            addAletheStep(AletheRule::CONTRACTION, vp3, vp3, {vp2b}, {}, *cdp);
      }

      Node vp8 = nm->mkNode(
          Kind::SEXPR, d_cl, nm->mkNode(Kind::IMPLIES, andNode, children[0]));

      Node vp4 = nm->mkNode(Kind::SEXPR, d_cl, vp8[1], andNode);
      success &=
          addAletheStep(AletheRule::IMPLIES_NEG1, vp4, vp4, {}, {}, *cdp);

      Node vp5 = nm->mkNode(Kind::SEXPR, d_cl, vp8[1], children[0]);
      success &= addAletheStep(AletheRule::RESOLUTION,
                               vp5,
                               vp5,
                               {vp4, vp3},
                               d_resPivots ? std::vector<Node>{andNode, d_true}
                                           : std::vector<Node>(),
                               *cdp);

      Node vp6 = nm->mkNode(Kind::SEXPR, d_cl, vp8[1], children[0].notNode());
      success &=
          addAletheStep(AletheRule::IMPLIES_NEG2, vp6, vp6, {}, {}, *cdp);

      Node vp7 = nm->mkNode(Kind::SEXPR, d_cl, vp8[1], vp8[1]);
      success &=
          addAletheStep(AletheRule::RESOLUTION,
                        vp7,
                        vp7,
                        {vp5, vp6},
                        d_resPivots ? std::vector<Node>{children[0], d_true}
                                    : std::vector<Node>(),
                        *cdp);

      if (children[0] != d_false)
      {
        success &=
            addAletheStep(AletheRule::CONTRACTION, res, vp8, {vp7}, {}, *cdp);
      }
      else
      {
        success &=
            addAletheStep(AletheRule::CONTRACTION, vp8, vp8, {vp7}, {}, *cdp);

        Node vp9 =
            nm->mkNode(Kind::SEXPR,
                       d_cl,
                       nm->mkNode(Kind::EQUAL, vp8[1], andNode.notNode()));
        success &=
            addAletheStep(AletheRule::IMPLIES_SIMPLIFY, vp9, vp9, {}, {}, *cdp);

        Node vp10 =
            nm->mkNode(Kind::SEXPR, d_cl, vp8[1].notNode(), andNode.notNode());
        success &=
            addAletheStep(AletheRule::EQUIV1, vp10, vp10, {vp9}, {}, *cdp);

        success &= addAletheStep(AletheRule::RESOLUTION,
                                 res,
                                 nm->mkNode(Kind::SEXPR, d_cl, res),
                                 {vp8, vp10},
                                 d_resPivots ? std::vector<Node>{vp8[1], d_true}
                                             : std::vector<Node>(),
                                 *cdp);
      }

      return success;
    }
    // The conversion is into a "rare_rewrite" step where the first argument is
    // a string literal with the name of the rewrite, followed by the arguments,
    // where lists are built using the Alethe operator "rare-list", which takes
    // 0 or more arguments.
    case ProofRule::DSL_REWRITE:
    {
      // get the name
      ProofRewriteRule di;
      Node rule;
      if (rewriter::getRewriteRule(args[0], di))
      {
        std::stringstream ss;
        ss << "\"" << di << "\"";
        rule = nm->mkRawSymbol(ss.str(), nm->sExprType());
      }
      else
      {
        Unreachable();
      }
      new_args.push_back(rule);
      for (int i = 1, size = args.size(); i < size; i++)
      {
        if (!args[i].isNull())
        {
          if (args[i].toString() == "")
          {  // TODO: better way
            new_args.push_back(nm->mkBoundVar("rare-list", nm->sExprType()));
          }
          else if (args[i].getKind() == Kind::SEXPR)
          {
            std::vector<Node> list_arg{
                nm->mkBoundVar("rare-list", nm->sExprType())};
            list_arg.insert(list_arg.end(), args[i].begin(), args[i].end());
            new_args.push_back(nm->mkNode(Kind::SEXPR, list_arg));
          }
          else
          {
            new_args.push_back(args[i]);
          }
        }
      }
      return addAletheStep(AletheRule::RARE_REWRITE,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           new_args,
                           *cdp);
    }
    case ProofRule::THEORY_REWRITE:
    {
      ProofRewriteRule di;
      if (rewriter::getRewriteRule(args[0], di))
      {
        return updateTheoryRewriteProofRewriteRule(
            res, id, children, args, cdp, continueUpdate, di);
      }
      return addAletheStep(AletheRule::HOLE,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           new_args,
                           *cdp);
    }
    case ProofRule::ARITH_POLY_NORM:
    {
      Assert(res.getNumChildren() >= 2);
      if (res[0] == res[1]) {
        return addAletheStep(
            AletheRule::REFL,
            res,
            nm->mkNode(Kind::SEXPR, d_cl, res),
            children,
	    {},
            *cdp);
      }
      else {
	bool success;
        // std::cout << "res " << res << std::endl;
        TypeNode tn1 = res[0].getType();

        TypeNode tn2 = res[1].getType();
        auto a= mkPolyNorm(res[0],tn1,cdp);
        // std::cout << "ready res[0]" << std::endl;
        Node LHS = a.theory::arith::PolyNorm::toNode(tn1);
        // std::cout << "Finished LHS " << LHS << std::endl;
        // std::cout << "res[1]" << res[1] << std::endl;
        Node RHS =
            mkPolyNorm(res[1], tn2, cdp).theory::arith::PolyNorm::toNode(tn2);
        // Node RHS =
        // theory::arith::PolyNorm::mkPolyNorm(res[1]).theory::arith::PolyNorm::toNode(tn2);
        // std::cout << "ready res[1]" << std::endl;
        // std::cout << "RHS " << RHS << std::endl;
        // std::cout << "LHS " << LHS << std::endl;
        // Assert(LHS = RHS);
        Node vp1 = nm->mkNode(Kind::EQUAL, res[0], LHS);
        Node vp2 = nm->mkNode(Kind::EQUAL, res[1], RHS);
        Node vp3 = nm->mkNode(Kind::EQUAL, RHS, res[1]);
        if (vp2 != vp3){ 
	  addAletheStep(
	    AletheRule::SYMM,
	    vp3,
	    nm->mkNode(Kind::SEXPR, d_cl, vp3),
	    {vp2},
	    {},
	    *cdp);
	}
	return addAletheStep(
	  AletheRule::TRANS,
	  res,
	  nm->mkNode(Kind::SEXPR, d_cl, res),
	  {vp1,vp3},
	  {},
	  *cdp);
      }
      return addAletheStep(AletheRule::HOLE,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           {},
                           {},
                           *cdp);
    }
    case ProofRule::ARITH_POLY_NORM_REL:
    {
      /**
            bool success = true;
            Kind diamond = res[0].getKind();
            //Assert(diamond = res[1].getKind());

            Node X = res[0];
            Node x1 = X[0];
            Node x2 = X[1];

            Node Y = res[1];
            Node y1 = Y[0];
            Node y2 = Y[1];

            if (x1.getType() == nm->integerType() && children[0][0][0].getType()
      == nm->realType()){ return  addAletheStep(AletheRule::HOLE, res,
      nm->mkNode(Kind::SEXPR,d_cl,res),{},{},*cdp);


            }
            TypeNode t_x = x1.getType();
            TypeNode t_y = y1.getType();
            Node n_x1 =
      mkPolyNorm(x1,t_x,cdp).theory::arith::PolyNorm::toNode(t_x); Node n_x2 =
      mkPolyNorm(x2,t_x,cdp).theory::arith::PolyNorm::toNode(t_x);
            //std::cout << "Finished x" << std::endl;

          // std::cout << "y1 " << y1 << std::endl;
            Node n_y1 =
      mkPolyNorm(y1,t_y,cdp).theory::arith::PolyNorm::toNode(t_y);
          // std::cout << "y2 " << y2 << std::endl;
            Node n_y2 =
      mkPolyNorm(y2,t_y,cdp).theory::arith::PolyNorm::toNode(t_y);

            //std::cout << "Finished y2" << std::endl;
      **/

      /*
            Node n_x1 =
         theory::arith::PolyNorm::mkPolyNorm(x1).theory::arith::PolyNorm::toNode(t_x);
            Node n_x2 =
         theory::arith::PolyNorm::mkPolyNorm(x2).theory::arith::PolyNorm::toNode(t_x);
            Node n_y1 =
         theory::arith::PolyNorm::mkPolyNorm(y1).theory::arith::PolyNorm::toNode(t_x);
            Node n_y2 =
         theory::arith::PolyNorm::mkPolyNorm(y2).theory::arith::PolyNorm::toNode(t_x);
        */

      /**      Node n_X = nm->mkNode(diamond,n_x1,n_x2);
            Node n_Y = nm->mkNode(diamond,n_y1,n_y2);
            Node X_n_X = nm->mkNode(Kind::EQUAL, X, n_X); //already proven

              success &= addAletheStep(AletheRule::HOLE, X_n_X,
      nm->mkNode(Kind::SEXPR,d_cl,X_n_X),{},{},*cdp); //TEMP Node Y_n_Y =
      nm->mkNode(Kind::EQUAL, Y, n_Y); //already proven success &=
      addAletheStep(AletheRule::HOLE, Y_n_Y,
      nm->mkNode(Kind::SEXPR,d_cl,Y_n_Y),{},{},*cdp); //TEMP Node n_Y_Y =
      nm->mkNode(Kind::EQUAL, n_Y, Y); Node n_X_Y = nm->mkNode(Kind::EQUAL, n_X,
      Y); Node n_X_n_Y = nm->mkNode(Kind::EQUAL, n_X, n_Y); Node n_res =
      nm->mkNode(Kind::EQUAL, n_X, n_Y);

            Node c = children[0];
            Node cX = c[0];
            Node cY = c[1];
            Node cX_cY = nm->mkNode(Kind::EQUAL,cX,cY);
            Node n_cX =
      mkPolyNorm(cX,t_x,cdp).theory::arith::PolyNorm::toNode(t_x);
            //Node n_cX =
      theory::arith::PolyNorm::mkPolyNorm(cX).theory::arith::PolyNorm::toNode(t_x);
            Node n_cY =
      mkPolyNorm(cY,t_x,cdp).theory::arith::PolyNorm::toNode(t_x);
            //Node n_cY =
      theory::arith::PolyNorm::mkPolyNorm(cY).theory::arith::PolyNorm::toNode(t_x);
            Node cX_n_cX = nm->mkNode(Kind::EQUAL, cX, n_cX); //already proven
              success &= addAletheStep(AletheRule::HOLE, cX_n_cX,
      nm->mkNode(Kind::SEXPR,d_cl,cX_n_cX),{},{},*cdp); //TEMP Node cY_n_cY =
      nm->mkNode(Kind::EQUAL, cY, n_cY); //already proven success &=
      addAletheStep(AletheRule::HOLE, cY_n_cY,
      nm->mkNode(Kind::SEXPR,d_cl,cY_n_cY),{},{},*cdp); //TEMP Node cX_n_cY =
      nm->mkNode(Kind::EQUAL, cX, n_cY); Node n_cX_n_cY =
      nm->mkNode(Kind::EQUAL, n_cX, n_cY); Node n_cX_cX =
      nm->mkNode(Kind::EQUAL, n_cX, cX);
      **/

      /*
      c is (= cX cY)

      ------------ p       ---------premise  ------------ p
       (= cX n_cX)         (= cX cY)          (= cY n_cY)
      ------------SYMM  -----------------------------------  TRANS
       (= n_cX cX)        (= cX n_cY)
      -----------------------------------  TRANS
          (= n_cX n_cY)
      */

      /**
      Assert(children[0] == cX_cY);
      if (cY != n_cY ){
            success &= addAletheStep(AletheRule::TRANS, cX_n_cY,
      nm->mkNode(Kind::SEXPR, d_cl, cX_n_cY), {cX_cY,cY_n_cY},{},*cdp);
      }
      if (n_cX != cX){
        success &= addAletheStep(AletheRule::SYMM, n_cX_cX,
      nm->mkNode(Kind::SEXPR, d_cl, n_cX_cX), {cX_n_cX},{},*cdp); success &=
      addAletheStep(AletheRule::TRANS, n_cX_n_cY, nm->mkNode(Kind::SEXPR, d_cl,
      n_cX_n_cY), {n_cX_cX,cX_n_cY},{},*cdp);
      }
      **/
      /*

       --------------------------------------------------- LIA_GENERIC      T1
        vp2: (cl (not (= n_cX n_cY)) n_X n_Y)                (= n_cX n_cY)
      ---------------------------------------------------------------------------------------
      RESOLUTION vp3: (cl (not n_X) n_Y)

      ------------------------------ equiv_neg2
        vp1: (cl (= n_X n_Y) n_X n_Y)                                  vp3

      -----------------------------------------------------------------------------------------------------------------
      RESOLUTION (cl (= n_X n_Y))




      */
      /* Node vp1 = nm->mkNode(Kind::OR, n_X_n_Y, n_X, n_Y);
       Node vp2 = nm->mkNode(Kind::OR, n_X.notNode(), n_Y, n_cX_n_cY.notNode());
       Node vp3 = nm->mkNode(Kind::OR, n_X.notNode(),n_Y);
       success &= addAletheStepFromOr(AletheRule::EQUIV_NEG2, vp1, {},{},*cdp);
       success &= addAletheStepFromOr(AletheRule::LIA_GENERIC, vp2, {},{},*cdp);
       success &= addAletheStepFromOr(AletheRule::TH_RESOLUTION, vp3,
 {n_cX_n_cY,vp2},d_resPivots ? std::vector<Node>{n_X.notNode(), n_Y.notNode()}
                      : std::vector<Node>()
 ,*cdp);
       success &= addAletheStep(AletheRule::RESOLUTION, n_X_n_Y,
 nm->mkNode(Kind::SEXPR,d_cl,n_X_n_Y),{vp3,vp1},{},*cdp);
 */
      /**
            Node vp2 = nm->mkNode(Kind::OR, n_X_n_Y, n_cX_n_cY.notNode());
            success &= addAletheStepFromOr(AletheRule::LIA_GENERIC, vp2,
      {},{},*cdp); success &= addAletheStep(AletheRule::TH_RESOLUTION, n_X_n_Y,
      nm->mkNode(Kind::SEXPR,d_cl,n_X_n_Y),{n_cX_n_cY,vp2},d_resPivots ?
      std::vector<Node>{n_cX_n_cY} : std::vector<Node>()
      ,*cdp);
      **/

      /*

                                                                (Y = n_Y)
                                                              ------------ SYMM
                            (n_X = n_Y)   		          (n_Y = Y)
                          ------------------------------------------------ TRANS
                             (n_X = Y)
          ---------p
          (X = n_X)
          -------------------------------------
                              X=Y
      */
      /**     if (n_Y != Y) {
             success &= addAletheStep(AletheRule::SYMM, n_Y_Y,
         nm->mkNode(Kind::SEXPR,d_cl,n_Y_Y),{Y_n_Y},{},*cdp); success &=
         addAletheStep(AletheRule::TRANS, n_X_Y,
         nm->mkNode(Kind::SEXPR,d_cl,n_X_Y),{n_X_n_Y,n_Y_Y},{},*cdp);
           }
           if (X != n_X) {
             success &= addAletheStep(AletheRule::TRANS, res,
         nm->mkNode(Kind::SEXPR,d_cl,res),{X_n_X,n_X_Y},{},*cdp);
           }
           else{//should not be necessary... try out
            success &= addAletheStep(AletheRule::HOLE, res,
         nm->mkNode(Kind::SEXPR,d_cl,res),{},{},*cdp);
           }

           return success; **/
      return addAletheStep(AletheRule::HOLE,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           {},
                           {},
                           *cdp);
    }
    // EVALUATE, which is used by the RARE elaboration, is captured by the "rare_rewrite" rule.
    case ProofRule::EVALUATE:
    {
      return addAletheStep(AletheRule::RARE_REWRITE,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           {nm->mkRawSymbol("\"evaluate\"", nm->sExprType())},
                           *cdp);
    }
      //
      //
      // First flatten, then simplify (everything or_simplify/and_simpify do
      // which includes idempotency + shuffling) res=(res[0] = res[1]) Note:
      // res[1] != simplify(flatten(res[0])) because simplify is stronger than
      // the simplification ACI_norm does. We are however using the invariant
      // that simplify(flatten(res[0])) and simplify(flatten(res[1])) consists
      // of the same literals but might be shuffeled.
      //
      //
      // VP1: (cl (res[0] = flatten(res[0])))
      // VP2: (cl (flatten(res[0]) = simplify(flatten(res[0]))))
      // VP3: (cl (res[0] = simplify(flatten(res[0]))))
      // VP4a: (cl (res[1] = flatten(res[1])))
      // VP4b (cl (flatten(res[1]) = (simplify(flatten(res[1])))))
      // VP4: (cl (res[1] = simplify(flatten(res[1]))))
      // VP5: (cl ((simplify(flatten(res[1]))) = simplify(flatten(res[0]))))
      // VP6: (cl (res[1] = simplify(flatten(res[0]))))
      // VP7: (cl (simplify(flatten(res[0]) = res[1])))
      //
      //
      // For the LHS
      // T1:
      //
      //            -------------- AC_SIMP     -------------
      //            OR_SIMPLIFY/AND_SIMPLIFY
      //  	     VP1                      VP2
      //            ---------------------------------------- TRANS
      //                            VP3
      //
      // For the RHS
      // T2:
      //
      //
      //  -------- AC_SIMP   ------- OR_SIMPLIFY/AND_SIMPLIFY
      //    VP4a              VP4b
      //  -------------------------- TRANS
      //            VP4
      //
      //
      // Putting both together
      //
      //                     ------- SHUFFLE
      //   T2                  VP5
      // ---------------------------------- TRANS
      //             VP6
      // ---------------------------------- SYMM
      //                          VP7
      // ------------------------------------------------- TRANS
      //                    res
      //
      //
      // If neither flattening nor simplification took place we ouput a EQ_REFL
      // step TODO: Currently still AC_NORM, might not be bad though
      //
      // If no flattening took place, i.e. flatten(r[0])=r[0] T1 is simplified
      // to
      //
      // ---------------------- OR_SIMPLIFY
      //        VP3
      //
      // If no simplification took place, T2 can be avoided completely and the
      // only step that remains of T1 is the ac_simp step

    case ProofRule::ACI_NORM:
    {
      Kind k_LHS = res[0].getKind();
      bool LHS_is_atom = !(k_LHS == Kind::AND || k_LHS == Kind::OR);
      Kind k_RHS = res[1].getKind();
      bool RHS_is_atom = !(k_RHS == Kind::AND || k_RHS == Kind::OR);
      if (!LHS_is_atom || !RHS_is_atom){
        bool success = true;
        std::map<Node,Node> emptyMap;
	
        //LHS Transformation, T1:
        Node flattenedLHS = applyAcSimp(emptyMap,res[0]);
        Node vp1 = nm->mkNode(Kind::EQUAL,res[0],flattenedLHS);
        success &=
           addAletheStep(AletheRule::AC_SIMP,
                         vp1,
                         nm->mkNode(Kind::SEXPR, d_cl, vp1),
                         {},
			 {},
			 *cdp);
        Node child_LHS = vp1;         
       	if (!LHS_is_atom) {
	  Node simplifiedFlattenedLHS = applyNarySimplify(flattenedLHS);
          Trace("alethe-proof") << "Flattened and simplified LHS " << simplifiedFlattenedLHS << std::endl;
          AletheRule simplify_rule = (k_LHS == Kind::AND) ? AletheRule::AND_SIMPLIFY : AletheRule::OR_SIMPLIFY;
          Node vp2 = nm->mkNode(Kind::EQUAL,flattenedLHS,simplifiedFlattenedLHS);
          Node vp3 = nm->mkNode(Kind::EQUAL,res[0],simplifiedFlattenedLHS);
          success &= addAletheStep(simplify_rule,
                         vp2,
                         nm->mkNode(Kind::SEXPR, d_cl, vp2),
                         {},
			 {},
			 *cdp) &&
	    addAletheStep(AletheRule::TRANS,
                         vp3,
                         nm->mkNode(Kind::SEXPR, d_cl, vp3),
                         {vp1,vp2},
			 {},
			 *cdp);
           child_LHS = vp3;

        }

       	//RHS Transformation, T2:
        Node flattenedRHS = applyAcSimp(emptyMap,res[1]);
        Node vp4 = nm->mkNode(Kind::EQUAL,res[1],flattenedRHS);
        success &= addAletheStep(AletheRule::AC_SIMP,
                         vp4,
                         nm->mkNode(Kind::SEXPR, d_cl, vp4),
                         {},
			 {},
			 *cdp);

        Node child_RHS = vp4;         
        if (!RHS_is_atom) {
	  Node simplifiedFlattenedRHS = applyNarySimplify(flattenedRHS);
          Trace("alethe-proof") << "Flattened and simplified RHS " << simplifiedFlattenedRHS << std::endl; 
          AletheRule simplify_rule = (k_RHS == Kind::AND) ? AletheRule::AND_SIMPLIFY : AletheRule::OR_SIMPLIFY;
          Node vp5 = nm->mkNode(Kind::EQUAL,flattenedRHS,simplifiedFlattenedRHS);
          Node vp6 = nm->mkNode(Kind::EQUAL,res[1],simplifiedFlattenedRHS);
          success &= addAletheStep(simplify_rule,
                         vp5,
                         nm->mkNode(Kind::SEXPR, d_cl, vp5),
                         {},
			 {},
			 *cdp) &&
	    addAletheStep(AletheRule::TRANS,
                         vp6,
                         nm->mkNode(Kind::SEXPR, d_cl, vp6),
                         {vp4,vp5},
			 {},
			 *cdp);

           child_RHS = vp6;
        }

	Node simplifiedFlattenedRHS = child_RHS[1];
	Node simplifiedFlattenedLHS = child_LHS[1];

	Node vp6 = nm->mkNode(Kind::EQUAL,simplifiedFlattenedRHS, simplifiedFlattenedLHS);
	Node vp7 = nm->mkNode(Kind::EQUAL,res[1], simplifiedFlattenedLHS);
	Node vp8 = nm->mkNode(Kind::EQUAL,simplifiedFlattenedLHS,res[1]);
 

	//Putting together:
	success &=
           addAletheStep(AletheRule::SHUFFLE,
                         vp6,
                         nm->mkNode(Kind::SEXPR, d_cl, vp6),
                         {},
			 {},
			 *cdp)
           &&
           addAletheStep(AletheRule::TRANS,
                         vp7,
                         nm->mkNode(Kind::SEXPR, d_cl, vp7),
                         {child_RHS,vp6},
			 {},
			 *cdp)
           &&
           addAletheStep(AletheRule::SYMM,
                         vp8,
                         nm->mkNode(Kind::SEXPR, d_cl, vp8),
                         {vp7},
			 {},
			 *cdp)
           &&
           addAletheStep(AletheRule::TRANS,
                         res,
                         nm->mkNode(Kind::SEXPR, d_cl, res),
                         {child_LHS,vp8},
			 {},
			 *cdp);

      }
      else if (k_LHS == Kind::BITVECTOR_AND || k_RHS == Kind::BITVECTOR_OR)
      {
	// This will be supported in the future
        return addAletheStep(AletheRule::HOLE,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
			   new_args,
			   *cdp);
      }
      else if (expr::isAssocCommIdem(k_LHS) || expr::isAssoc(k_LHS) || expr::isAssocCommIdem(k_RHS) || expr::isAssoc(k_LHS))
      {
        return addAletheStep(AletheRule::HOLE,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
			   new_args,
			   *cdp);
      }
      // For all other operators getACINormalForm returns the unchanged term
      return addAletheStep(AletheRule::EQ_REFLEXIVE,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           new_args,
			   *cdp);
    }
    // If the trusted rule is a theory lemma from arithmetic, we try to phrase
    // it with "lia_generic".
    case ProofRule::TRUST:
    {
      // check for case where the trust step is introducing an equality between
      // a term and another whose Alethe conversion is itself, in which case we
      // justify this as a REFL step. This happens with trusted purification
      // steps, for example.
      Node resConv = d_anc.maybeConvert(res);
      if (!resConv.isNull() && resConv.getKind() == Kind::EQUAL
          && resConv[0] == resConv[1])
      {
        return addAletheStep(AletheRule::REFL,
                             res,
                             nm->mkNode(Kind::SEXPR, d_cl, res),
                             children,
                             {},
                             *cdp);
      }
      TrustId tid;
      bool hasTrustId = getTrustId(args[0], tid);
      if (hasTrustId && tid == TrustId::THEORY_LEMMA)
      {
        // if we are in the arithmetic case, we rather add a LIA_GENERIC step
        if (res.getKind() == Kind::NOT && res[0].getKind() == Kind::AND)
        {
          Trace("alethe-proof") << "... test each arg if ineq\n";
          bool allIneqs = true;
          for (const Node& arg : res[0])
          {
            Node toTest = arg.getKind() == Kind::NOT ? arg[0] : arg;
            Kind k = toTest.getKind();
            if (k != Kind::LT && k != Kind::LEQ && k != Kind::GT
                && k != Kind::GEQ && k != Kind::EQUAL)
            {
              Trace("alethe-proof") << "... arg " << arg << " not ineq\n";
              allIneqs = false;
              break;
            }
          }
          if (allIneqs)
          {
            return addAletheStep(AletheRule::LIA_GENERIC,
                                 res,
                                 nm->mkNode(Kind::SEXPR, d_cl, res),
                                 children,
                                 {},
                                 *cdp);
          }
        }
      }
      std::stringstream ss;
      if (hasTrustId)
      {
        cvc5::internal::theory::TheoryId thid;
        bool hasTheoryId = theory::builtin::BuiltinProofRuleChecker::getTheoryId(args[0], thid);
        if (hasTheoryId){
          ss << "\"" << tid << "\" \"" << thid << "\"";
	}
        else{
          ss << "\"" << tid << "\"";
        }
      }
      else
      {
        ss << "\"" << args[0] << "\"";
      }
      std::vector<Node> newArgs{nm->mkRawSymbol(ss.str(), nm->sExprType())};
      newArgs.insert(newArgs.end(), args.begin() + 1, args.end());
      return addAletheStep(AletheRule::HOLE,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           newArgs,
                           *cdp);
    }
    // ======== Resolution and N-ary Resolution
    // Because the RESOLUTION rule is merely a special case of CHAIN_RESOLUTION,
    // the same translation can be used for both.
    //
    // The main complication for the translation of the rule is that in the case
    // that the conclusion is (or G1 ... Gn), the result is ambigous. E.g.,
    //
    // (cl F1 (or F2 F3))    (cl (not F1))
    // -------------------------------------- resolution
    // (cl (or F2 F3))
    //
    // (cl F1 F2 F3)         (cl (not F1))
    // -------------------------------------- resolution
    // (cl F2 F3)
    //
    // both (cl (or F2 F3)) and (cl F2 F3) could be represented by the same node
    // (or F2 F3). Thus, it has to be checked if the conclusion C is a singleton
    // clause or not.
    //
    // If C = (or F1 ... Fn) is a non-singleton clause, then:
    //
    //   VP1 ... VPn
    // ------------------ resolution
    //  (cl F1 ... Fn)*
    //
    // Else if, C = false:
    //
    //   VP1 ... VPn
    // ------------------ resolution
    //       (cl)*
    //
    // Otherwise:
    //
    //   VP1 ... VPn
    // ------------------ resolution
    //      (cl C)*
    //
    //  * the corresponding proof node is C
    case ProofRule::RESOLUTION:
    case ProofRule::CHAIN_RESOLUTION:
    case ProofRule::MACRO_RESOLUTION:
    case ProofRule::MACRO_RESOLUTION_TRUST:
    {
      std::vector<Node> cargs;
      if (id == ProofRule::CHAIN_RESOLUTION)
      {
        for (size_t i = 0, nargs = args[0].getNumChildren(); i < nargs; i++)
        {
          cargs.push_back(args[0][i]);
          cargs.push_back(args[1][i]);
        }
      }
      else if (id == ProofRule::MACRO_RESOLUTION
               || id == ProofRule::MACRO_RESOLUTION_TRUST)
      {
        cargs.insert(cargs.end(), args.begin() + 1, args.end());
      }
      else
      {
        cargs = args;
      }
      Node conclusion;
      if (!isSingletonClause(res, children, cargs))
      {
        std::vector<Node> concChildren{d_cl};
        concChildren.insert(concChildren.end(), res.begin(), res.end());
        conclusion = nm->mkNode(Kind::SEXPR, concChildren);
      }
      else if (res == d_false)
      {
        conclusion = nm->mkNode(Kind::SEXPR, d_cl);
      }
      else
      {
        conclusion = nm->mkNode(Kind::SEXPR, d_cl, res);
      }
      // checker expects opposite order. We always keep the pivots because we
      // need them to compute in updatePost whether we will add OR steps. If
      // d_resPivots is off we will remove the pivots after that.
      std::vector<Node> newArgs;
      for (size_t i = 0, size = cargs.size(); i < size; i = i + 2)
      {
        newArgs.push_back(cargs[i + 1]);
        newArgs.push_back(cargs[i]);
      }
      return addAletheStep(
          AletheRule::RESOLUTION_OR, res, conclusion, children, newArgs, *cdp);
    }
    // ======== Factoring
    // See proof_rule.h for documentation on the FACTORING rule. This comment
    // uses variable names as introduced there.
    //
    // If C2 = (or F1 ... Fn) but C1 != (or C2 ... C2), then VC2 = (cl F1 ...
    // Fn) Otherwise, VC2 = (cl C2).
    //
    //    P
    // ------- contraction
    //   VC2*
    //
    // * the corresponding proof node is C2
    case ProofRule::FACTORING:
    {
      if (res.getKind() == Kind::OR)
      {
        for (const Node& child : children[0])
        {
          if (child != res)
          {
            return addAletheStepFromOr(
                AletheRule::CONTRACTION, res, children, {}, *cdp);
          }
        }
      }
      return addAletheStep(AletheRule::CONTRACTION,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Reordering
    // This rule is translated according to the clauses pattern.
    case ProofRule::REORDERING:
    {
      return addAletheStepFromOr(
          AletheRule::REORDERING, res, children, {}, *cdp);
    }
    // ======== Split
    // See proof_rule.h for documentation on the SPLIT rule. This comment
    // uses variable names as introduced there.
    //
    // --------- not_not      --------- not_not
    //    VP1                    VP2
    // -------------------------------- resolution
    //          (cl F (not F))*
    //
    // VP1: (cl (not (not (not F))) F)
    // VP2: (cl (not (not (not (not F)))) (not F))
    //
    // * the corresponding proof node is (or F (not F))
    case ProofRule::SPLIT:
    {
      Node vp1 = nm->mkNode(
          Kind::SEXPR, d_cl, args[0].notNode().notNode().notNode(), args[0]);
      Node vp2 = nm->mkNode(Kind::SEXPR,
                            d_cl,
                            args[0].notNode().notNode().notNode().notNode(),
                            args[0].notNode());
      return addAletheStep(AletheRule::NOT_NOT, vp2, vp2, {}, {}, *cdp)
             && addAletheStep(AletheRule::NOT_NOT, vp1, vp1, {}, {}, *cdp)
             && addAletheStepFromOr(
                 AletheRule::RESOLUTION,
                 res,
                 {vp1, vp2},
                 d_resPivots
                     ? std::vector<Node>{args[0].notNode().notNode().notNode(),
                                         d_true}
                     : std::vector<Node>(),
                 *cdp);
    }
    // ======== Equality resolution
    //
    //  ------ EQUIV_POS2
    //   VP1                P2    P1
    //  --------------------------------- resolution
    //              (cl F2)*
    //
    // VP1: (cl (not (= F1 F2)) (not F1) F2)
    //
    // * the corresponding proof node is F2
    case ProofRule::EQ_RESOLVE:
    {
      Node equivPos2Cl =
          nm->mkNode(Kind::SEXPR,
                     {d_cl, children[1].notNode(), children[0].notNode(), res});
      bool success = addAletheStep(
          AletheRule::EQUIV_POS2, equivPos2Cl, equivPos2Cl, {}, {}, *cdp);
      // we will use an RESOLUTION_OR step for the resolution because the proof
      // of children[0], if it is for (or t1 ... tn), may actually conclude  (cl
      // t1 ... tn). Using RESOLUTION_OR will guarantee that in post-visit time
      // the resolution step is fixed if need be
      return success
             && addAletheStep(
                 AletheRule::RESOLUTION_OR,
                 res,
                 nm->mkNode(Kind::SEXPR, d_cl, res),
                 {equivPos2Cl, children[1], children[0]},
                 std::vector<Node>{children[1], d_false, children[0], d_false},
                 *cdp);
    }
    // ======== Modus ponens
    // See proof_rule.h for documentation on the MODUS_PONENS rule. This comment
    // uses variable names as introduced there.
    //
    //     (P2:(=> F1 F2))
    // ------------------------ implies
    //  (VP1:(cl (not F1) F2))             (P1:F1)
    // -------------------------------------------- resolution
    //                   (cl F2)*
    //
    // * the corresponding proof node is F2
    case ProofRule::MODUS_PONENS:
    {
      Node vp1 = nm->mkNode(Kind::SEXPR, d_cl, children[0].notNode(), res);
      return addAletheStep(
                 AletheRule::IMPLIES, vp1, vp1, {children[1]}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(Kind::SEXPR, d_cl, res),
                              {vp1, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== Double negation elimination
    // See proof_rule.h for documentation on the NOT_NOT_ELIM rule. This comment
    // uses variable names as introduced there.
    //
    // ---------------------------------- not_not
    //  (VP1:(cl (not (not (not F))) F))           (P:(not (not F)))
    // ------------------------------------------------------------- resolution
    //                            (cl F)*
    //
    // * the corresponding proof node is F
    case ProofRule::NOT_NOT_ELIM:
    {
      Node vp1 = nm->mkNode(Kind::SEXPR, d_cl, children[0].notNode(), res);

      return addAletheStep(AletheRule::NOT_NOT, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(Kind::SEXPR, d_cl, res),
                              {vp1, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== Contradiction
    // See proof_rule.h for documentation on the CONTRA rule. This
    // comment uses variable names as introduced there.
    //
    //  P1   P2
    // --------- resolution
    //   (cl)*
    //
    // * the corresponding proof node is false
    case ProofRule::CONTRA:
    {
      return addAletheStep(AletheRule::RESOLUTION,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl),
                           children,
                           d_resPivots ? std::vector<Node>{children[0], d_true}
                                       : std::vector<Node>(),
                           *cdp);
    }
    // ======== And elimination
    // This rule is translated according to the singleton pattern.
    case ProofRule::AND_ELIM:
    {
      return addAletheStep(AletheRule::AND,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           args,
                           *cdp);
    }
    // ======== And introduction
    // See proof_rule.h for documentation on the AND_INTRO rule. This
    // comment uses variable names as introduced there.
    //
    //
    // ----- and_neg
    //  VP1            P1 ... Pn
    // -------------------------- resolution
    //   (cl (and F1 ... Fn))*
    //
    // VP1:(cl (and F1 ... Fn) (not F1) ... (not Fn))
    //
    // * the corresponding proof node is (and F1 ... Fn)
    case ProofRule::AND_INTRO:
    {
      std::vector<Node> neg_Nodes = {d_cl, res};
      for (size_t i = 0, size = children.size(); i < size; i++)
      {
        neg_Nodes.push_back(children[i].notNode());
      }
      Node vp1 = nm->mkNode(Kind::SEXPR, neg_Nodes);

      std::vector<Node> new_children = {vp1};
      new_children.insert(new_children.end(), children.begin(), children.end());
      std::vector<Node> newArgs;
      if (d_resPivots)
      {
        for (const Node& child : children)
        {
          newArgs.push_back(child);
          newArgs.push_back(d_false);
        }
      }
      return addAletheStep(AletheRule::AND_NEG, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(Kind::SEXPR, d_cl, res),
                              new_children,
                              newArgs,
                              *cdp);
    }
    // ======== Not Or elimination
    // This rule is translated according to the singleton pattern.
    case ProofRule::NOT_OR_ELIM:
    {
      return addAletheStep(AletheRule::NOT_OR,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           args,
                           *cdp);
    }
    // ======== Implication elimination
    // This rule is translated according to the clause pattern.
    case ProofRule::IMPLIES_ELIM:
    {
      return addAletheStepFromOr(AletheRule::IMPLIES, res, children, {}, *cdp);
    }
    // ======== Not Implication elimination version 1
    // This rule is translated according to the singleton pattern.
    case ProofRule::NOT_IMPLIES_ELIM1:
    {
      return addAletheStep(AletheRule::NOT_IMPLIES1,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Not Implication elimination version 2
    // This rule is translated according to the singleton pattern.
    case ProofRule::NOT_IMPLIES_ELIM2:
    {
      return addAletheStep(AletheRule::NOT_IMPLIES2,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Various elimination rules
    // The following rules are all translated according to the clause pattern.
    case ProofRule::EQUIV_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::EQUIV1, res, children, {}, *cdp);
    }
    case ProofRule::EQUIV_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::EQUIV2, res, children, {}, *cdp);
    }
    case ProofRule::NOT_EQUIV_ELIM1:
    {
      return addAletheStepFromOr(
          AletheRule::NOT_EQUIV1, res, children, {}, *cdp);
    }
    case ProofRule::NOT_EQUIV_ELIM2:
    {
      return addAletheStepFromOr(
          AletheRule::NOT_EQUIV2, res, children, {}, *cdp);
    }
    case ProofRule::XOR_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::XOR1, res, children, {}, *cdp);
    }
    case ProofRule::XOR_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::XOR2, res, children, {}, *cdp);
    }
    case ProofRule::NOT_XOR_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::NOT_XOR1, res, children, {}, *cdp);
    }
    case ProofRule::NOT_XOR_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::NOT_XOR2, res, children, {}, *cdp);
    }
    case ProofRule::ITE_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::ITE2, res, children, {}, *cdp);
    }
    case ProofRule::ITE_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::ITE1, res, children, {}, *cdp);
    }
    case ProofRule::NOT_ITE_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::NOT_ITE2, res, children, {}, *cdp);
    }
    case ProofRule::NOT_ITE_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::NOT_ITE1, res, children, {}, *cdp);
    }
    //================================================= De Morgan rules
    // ======== Not And
    // This rule is translated according to the clause pattern.
    case ProofRule::NOT_AND:
    {
      return addAletheStepFromOr(AletheRule::NOT_AND, res, children, {}, *cdp);
    }

    //================================================= CNF rules
    // The following rules are all translated according to the clause pattern.
    case ProofRule::CNF_AND_POS:
    {
      return addAletheStepFromOr(AletheRule::AND_POS,
                                 res,
                                 children,
                                 std::vector<Node>{args.back()},
                                 *cdp);
    }
    case ProofRule::CNF_AND_NEG:
    {
      return addAletheStepFromOr(AletheRule::AND_NEG, res, children, {}, *cdp);
    }
    case ProofRule::CNF_OR_POS:
    {
      return addAletheStepFromOr(AletheRule::OR_POS, res, children, {}, *cdp);
    }
    case ProofRule::CNF_OR_NEG:
    {
      return addAletheStepFromOr(AletheRule::OR_NEG,
                                 res,
                                 children,
                                 std::vector<Node>{args.back()},
                                 *cdp);
    }
    case ProofRule::CNF_IMPLIES_POS:
    {
      return addAletheStepFromOr(
          AletheRule::IMPLIES_POS, res, children, {}, *cdp);
    }
    case ProofRule::CNF_IMPLIES_NEG1:
    {
      return addAletheStepFromOr(
          AletheRule::IMPLIES_NEG1, res, children, {}, *cdp);
    }
    case ProofRule::CNF_IMPLIES_NEG2:
    {
      return addAletheStepFromOr(
          AletheRule::IMPLIES_NEG2, res, children, {}, *cdp);
    }
    case ProofRule::CNF_EQUIV_POS1:
    {
      return addAletheStepFromOr(
          AletheRule::EQUIV_POS2, res, children, {}, *cdp);
    }
    case ProofRule::CNF_EQUIV_POS2:
    {
      return addAletheStepFromOr(
          AletheRule::EQUIV_POS1, res, children, {}, *cdp);
    }
    case ProofRule::CNF_EQUIV_NEG1:
    {
      return addAletheStepFromOr(
          AletheRule::EQUIV_NEG2, res, children, {}, *cdp);
    }
    case ProofRule::CNF_EQUIV_NEG2:
    {
      return addAletheStepFromOr(
          AletheRule::EQUIV_NEG1, res, children, {}, *cdp);
    }
    case ProofRule::CNF_XOR_POS1:
    {
      return addAletheStepFromOr(AletheRule::XOR_POS1, res, children, {}, *cdp);
    }
    case ProofRule::CNF_XOR_POS2:
    {
      return addAletheStepFromOr(AletheRule::XOR_POS2, res, children, {}, *cdp);
    }
    case ProofRule::CNF_XOR_NEG1:
    {
      return addAletheStepFromOr(AletheRule::XOR_NEG2, res, children, {}, *cdp);
    }
    case ProofRule::CNF_XOR_NEG2:
    {
      return addAletheStepFromOr(AletheRule::XOR_NEG1, res, children, {}, *cdp);
    }
    case ProofRule::CNF_ITE_POS1:
    {
      return addAletheStepFromOr(AletheRule::ITE_POS2, res, children, {}, *cdp);
    }
    case ProofRule::CNF_ITE_POS2:
    {
      return addAletheStepFromOr(AletheRule::ITE_POS1, res, children, {}, *cdp);
    }
    case ProofRule::CNF_ITE_NEG1:
    {
      return addAletheStepFromOr(AletheRule::ITE_NEG2, res, children, {}, *cdp);
    }
    case ProofRule::CNF_ITE_NEG2:
    {
      return addAletheStepFromOr(AletheRule::ITE_NEG1, res, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 3
    //
    // ----- ite_pos1            ----- ite_pos2
    //  VP1                       VP2
    // ------------------------------- resolution
    //             VP3
    // ------------------------------- reordering
    //             VP4
    // ------------------------------- contraction
    //  (cl (not (ite C F1 F2)) F1 F2)
    //
    // VP1: (cl (not (ite C F1 F2)) C F2)
    // VP2: (cl (not (ite C F1 F2)) (not C) F1)
    // VP3: (cl (not (ite C F1 F2)) F2 (not (ite C F1 F2)) F1)
    // VP4: (cl (not (ite C F1 F2)) (not (ite C F1 F2)) F1 F2)
    //
    // * the corresponding proof node is (or (not (ite C F1 F2)) F1 F2)
    case ProofRule::CNF_ITE_POS3:
    {
      Node vp1 = nm->mkNode(Kind::SEXPR, {d_cl, res[0], args[0][0], res[2]});
      Node vp2 =
          nm->mkNode(Kind::SEXPR, {d_cl, res[0], args[0][0].notNode(), res[1]});
      Node vp3 =
          nm->mkNode(Kind::SEXPR, {d_cl, res[0], res[2], res[0], res[1]});
      Node vp4 =
          nm->mkNode(Kind::SEXPR, {d_cl, res[0], res[0], res[1], res[2]});

      return addAletheStep(AletheRule::ITE_POS1, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::ITE_POS2, vp2, vp2, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              vp3,
                              vp3,
                              {vp1, vp2},
                              d_resPivots
                                  ? std::vector<Node>{args[0][0], d_true}
                                  : std::vector<Node>(),
                              *cdp)
             && addAletheStep(AletheRule::REORDERING, vp4, vp4, {vp3}, {}, *cdp)
             && addAletheStepFromOr(
                 AletheRule::CONTRACTION, res, {vp4}, {}, *cdp);
    }
    // ======== CNF ITE Neg version 3
    //
    // ----- ite_neg1            ----- ite_neg2
    //  VP1                       VP2
    // ------------------------------- resolution
    //             VP3
    // ------------------------------- reordering
    //             VP4
    // ------------------------------- contraction
    //  (cl (ite C F1 F2) C (not F2))
    //
    // VP1: (cl (ite C F1 F2) C (not F2))
    // VP2: (cl (ite C F1 F2) (not C) (not F1))
    // VP3: (cl (ite C F1 F2) (not F2) (ite C F1 F2) (not F1))
    // VP4: (cl (ite C F1 F2) (ite C F1 F2) (not F1) (not F2))
    //
    // * the corresponding proof node is (or (ite C F1 F2) C (not F2))
    case ProofRule::CNF_ITE_NEG3:
    {
      Node vp1 = nm->mkNode(Kind::SEXPR, {d_cl, res[0], args[0][0], res[2]});
      Node vp2 =
          nm->mkNode(Kind::SEXPR, {d_cl, res[0], args[0][0].notNode(), res[1]});
      Node vp3 =
          nm->mkNode(Kind::SEXPR, {d_cl, res[0], res[2], res[0], res[1]});
      Node vp4 =
          nm->mkNode(Kind::SEXPR, {d_cl, res[0], res[0], res[1], res[2]});

      return addAletheStep(AletheRule::ITE_NEG1, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::ITE_NEG2, vp2, vp2, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              vp3,
                              vp3,
                              {vp1, vp2},
                              d_resPivots
                                  ? std::vector<Node>{args[0][0], d_true}
                                  : std::vector<Node>(),
                              *cdp)
             && addAletheStep(AletheRule::REORDERING, vp4, vp4, {vp3}, {}, *cdp)
             && addAletheStepFromOr(
                 AletheRule::CONTRACTION, res, {vp4}, {}, *cdp);
    }
    //================================================= Equality rules
    // The following rules are all translated according to the singleton
    // pattern.
    case ProofRule::REFL:
    {
      return addAletheStep(AletheRule::REFL,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    case ProofRule::SYMM:
    {
      return addAletheStep(
          res.getKind() == Kind::NOT ? AletheRule::NOT_SYMM : AletheRule::SYMM,
          res,
          nm->mkNode(Kind::SEXPR, d_cl, res),
          children,
          {},
          *cdp);
    }
    case ProofRule::TRANS:
    {
      return addAletheStep(AletheRule::TRANS,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Congruence
    // In the case that the kind of the function symbol f? is FORALL or
    // EXISTS, the cong rule needs to be converted into a bind rule:
    //
    //  (cl (= F G))
    // -------------------- bind, z1 ... zn (= y1 z1) ... (= yn zn)
    //  (= (Q ((y1 T1) ... (yn Tn)) F) (Q ((z1 T1) ... (zn Tn)) G))
    //
    // Otherwise, the rule is regular congruence:
    //
    //    P1 ... Pn
    //  -------------------------------------------------------- cong
    //   (cl (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn)))
    case ProofRule::CONG:
    case ProofRule::NARY_CONG:
    {
      if (res[0].isClosure())
      {
        // collect rhs variables
        new_args.insert(new_args.end(), res[1][0].begin(), res[1][0].end());
        for (size_t i = 0, size = res[0][0].getNumChildren(); i < size; ++i)
        {
          new_args.push_back(res[0][0][i].eqNode(res[1][0][i]));
        }
        Kind k = res[0].getKind();
        return addAletheStep(AletheRule::ANCHOR_BIND,
                             res,
                             nm->mkNode(Kind::SEXPR, d_cl, res),
                             // be sure to ignore premise for pattern
                             (k == Kind::FORALL || k == Kind::EXISTS)
                                 ? std::vector<Node>{children[0]}
                                 : children,
                             new_args,
                             *cdp);
      }
      return addAletheStep(AletheRule::CONG,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    case ProofRule::HO_CONG:
    {
      return addAletheStep(AletheRule::HO_CONG,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== True intro
    //
    // ------------------------------- EQUIV_SIMPLIFY
    //  (VP1:(cl (= (= F true) F)))
    // ------------------------------- EQUIV2
    //  (VP2:(cl (= F true) (not F)))           P
    // -------------------------------------------- RESOLUTION
    //  (cl (= F true))*
    //
    // * the corresponding proof node is (= F true)
    case ProofRule::TRUE_INTRO:
    {
      Node vp1 = nm->mkNode(Kind::SEXPR, d_cl, res.eqNode(children[0]));
      Node vp2 = nm->mkNode(Kind::SEXPR, d_cl, res, children[0].notNode());
      return addAletheStep(AletheRule::EQUIV_SIMPLIFY, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::EQUIV2, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(Kind::SEXPR, d_cl, res),
                              {vp2, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== True elim
    //
    // ------------------------------- EQUIV_SIMPLIFY
    //  (VP1:(cl (= (= F true) F)))
    // ------------------------------- EQUIV1
    //  (VP2:(cl (not (= F true)) F))           P
    // -------------------------------------------- RESOLUTION
    //  (cl F)*
    //
    // * the corresponding proof node is F
    case ProofRule::TRUE_ELIM:
    {
      Node vp1 = nm->mkNode(Kind::SEXPR, d_cl, children[0].eqNode(res));
      Node vp2 = nm->mkNode(Kind::SEXPR, d_cl, children[0].notNode(), res);
      return addAletheStep(AletheRule::EQUIV_SIMPLIFY, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::EQUIV1, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(Kind::SEXPR, d_cl, res),
                              {vp2, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== False intro
    //
    // ----- EQUIV_SIMPLIFY
    //  VP1
    // ----- EQUIV2     ----- NOT_NOT
    //  VP2              VP3
    // ---------------------- RESOLUTION
    //          VP4                        P
    // -------------------------------------- RESOLUTION
    //          (cl (= F false))*
    //
    // VP1: (cl (= (= F false) (not F)))
    // VP2: (cl (= F false) (not (not F)))
    // VP3: (cl (not (not (not F))) F)
    // VP4: (cl (= F false) F)
    //
    // * the corresponding proof node is (= F false)
    case ProofRule::FALSE_INTRO:
    {
      Node vp1 = nm->mkNode(Kind::SEXPR, d_cl, res.eqNode(children[0]));
      Node vp2 = nm->mkNode(Kind::SEXPR, d_cl, res, children[0].notNode());
      Node vp3 = nm->mkNode(
          Kind::SEXPR, d_cl, children[0].notNode().notNode(), children[0][0]);
      Node vp4 = nm->mkNode(Kind::SEXPR, d_cl, res, children[0][0]);

      return addAletheStep(AletheRule::EQUIV_SIMPLIFY, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::EQUIV2, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::NOT_NOT, vp3, vp3, {}, {}, *cdp)
             && addAletheStep(
                 AletheRule::RESOLUTION,
                 vp4,
                 vp4,
                 {vp2, vp3},
                 d_resPivots ? std::vector<Node>{children[0].notNode(), d_true}
                             : std::vector<Node>(),
                 *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(Kind::SEXPR, d_cl, res),
                              {vp4, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0][0], d_true}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== False elim
    //
    // ----- EQUIV_SIMPLIFY
    //  VP1
    // ----- EQUIV1
    //  VP2                P
    // ---------------------- RESOLUTION
    //     (cl (not F))*
    //
    // VP1: (cl (= (= F false) (not F)))
    // VP2: (cl (not (= F false)) (not F))
    // VP3: (cl (not (not (not F))) F)
    // VP4: (cl (= F false) F)
    //
    // * the corresponding proof node is (not F)
    case ProofRule::FALSE_ELIM:
    {
      Node vp1 = nm->mkNode(Kind::SEXPR, d_cl, children[0].eqNode(res));
      Node vp2 = nm->mkNode(Kind::SEXPR, d_cl, children[0].notNode(), res);

      return addAletheStep(AletheRule::EQUIV_SIMPLIFY, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::EQUIV1, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(Kind::SEXPR, d_cl, res),
                              {vp2, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    //================================================= Skolems rules
    // ======== Skolem intro
    // Since this rule just equates a term to its purification skolem, whose
    // conversion is the term itself, the converted conclusion is an equality
    // between the same terms.
    case ProofRule::SKOLEM_INTRO:
    {
      return addAletheStep(AletheRule::REFL,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           {},
                           {},
                           *cdp);
    }
    // ======== Replace term by its axiom definition
    // For now this introduces a hole. The processing in the future should
    // generate corresponding Alethe steps for each particular axiom for term
    // removal (for example for the ITE case).
    case ProofRule::ITE_EQ:
    {
      return addAletheStep(AletheRule::HOLE,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           {},
                           {},
                           *cdp);
    }
    // ======== Skolemize
    // See proof_rule.h for documentation on the SKOLEMIZE rule. This
    // comment uses variable names as introduced there.
    //
    // In cvc5 this is applied solely to terms (not (forall (...)  F)),
    // concluding (not F*sigma'), where sigma' is the cumulative substitution
    // built from sigma1...sigma_n, and each sigma_i replaces xi by the choice
    // term (epsilon ((xi Ti)) (forall ((xi+1 Ti+1) ... (xn+1 Tn+1)) (not
    // F))). The resulting Alethe Skolemization step is:
    //
    //            ---------------- refl
    //             (= F F*sigma')
    //  ------------------------- anchor_sko_forall, sigma_1, ..., sigma_n
    //  (= (forall ((x1 T1) ... (xn Tn)) F) F*sigma')
    // ----------------------------------------------- cong
    //  (= (not (forall ((x1 T1) ... (xn Tn)) F)) (not F*sigma'))
    //
    // Then, we eliminate the equality to obtain (not F*sigma) from the premise:
    //
    //  ---- equiv_pos2
    //  VP1   (= (not (forall (...) F)) (not F*sigma'))   (not (forall (...) F))
    //  ------------------------------------------------------------- resolution
    //                           (not F*sigma')
    //
    // VP1 :
    //  (cl
    //    (not (= (not (forall (...) F)) (not F*sigma')))
    //    (not (not (forall (...) F)))
    //    (not F*sigma'))
    //
    // Note that F*sigma' is equivalent to F*sigma once its Skolem terms are
    // lifted to choice terms by the node converter.
    case ProofRule::SKOLEMIZE:
    {
      bool success = true;
      Node quant = children[0][0], skolemized = res[0];
      Assert(children[0].getKind() == Kind::NOT
             && children[0][0].getKind() == Kind::FORALL);
      Node eq = quant[1].eqNode(skolemized);
      // add rfl step for final replacement
      Node premise = nm->mkNode(Kind::SEXPR, d_cl, eq);
      success &=
          addAletheStep(AletheRule::REFL, premise, premise, {}, {}, *cdp);
      std::vector<Node> bVars{quant[0].begin(), quant[0].end()};
      std::vector<Node> skoSubstitutions;
      SkolemManager* sm = nm->getSkolemManager();
      const std::map<Node, Node>& skolemDefs = d_anc.getSkolemDefinitions();
      for (size_t i = 0, size = quant[0].getNumChildren(); i < size; ++i)
      {
        // Make the Skolem corresponding to this variable and retrieve its
        // conversion from the node converter
        std::vector<Node> cacheVals{quant, nm->mkConstInt(Rational(i))};
        Node sk =
            sm->mkSkolemFunction(SkolemId::QUANTIFIERS_SKOLEMIZE, cacheVals);
        Assert(!sk.isNull());
        if (options().proof.proofAletheDefineSkolems)
        {
          skoSubstitutions.push_back(quant[0][i].eqNode(sk));
          continue;
        }
        auto it = skolemDefs.find(sk);
        Assert(it != skolemDefs.end()) << sk << " " << skolemDefs;
        skoSubstitutions.push_back(quant[0][i].eqNode(it->second));
      }
      Assert(!d_anc.convert(quant.eqNode(skolemized)).isNull());
      Node conclusion = nm->mkNode(
          Kind::SEXPR, d_cl, d_anc.convert(quant.eqNode(skolemized)));
      // add the sko step
      success &= addAletheStep(AletheRule::ANCHOR_SKO_FORALL,
                               conclusion,
                               conclusion,
                               {premise},
                               skoSubstitutions,
                               *cdp);
      // add congruence step with NOT for the forall case
      Node newConclusion = nm->mkNode(
          Kind::SEXPR, d_cl, (quant.notNode()).eqNode(skolemized.notNode()));
      success &= addAletheStep(AletheRule::CONG,
                               newConclusion,
                               newConclusion,
                               {conclusion},
                               {},
                               *cdp);
      conclusion = newConclusion;
      // now equality resolution reasoning
      Node vp1 = nm->mkNode(
          Kind::SEXPR,
          {d_cl, conclusion[1].notNode(), children[0].notNode(), res});
      success &= addAletheStep(AletheRule::EQUIV_POS2, vp1, vp1, {}, {}, *cdp);
      return success
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(Kind::SEXPR, d_cl, res),
                              {vp1, conclusion, children[0]},
                              d_resPivots ? std::vector<Node>{conclusion[1],
                                                              d_false,
                                                              children[0],
                                                              d_false}
                                          : std::vector<Node>(),
                              *cdp);
    }
    // ======== Bitvector
    //
    // ------------------------ BV_BITBLAST_STEP_BV<KIND>
    //  (cl (= t bitblast(t)))
    case ProofRule::BV_EAGER_ATOM:
    {
      Assert(res.getKind() == Kind::EQUAL && res[0][0] == res[1]);
      Node newRes = res[0][0].eqNode(res[1]);
      return addAletheStep(AletheRule::REFL,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, newRes),
                           children,
                           {},
                           *cdp);
    }
    // ------------------------ BV_BITBLAST_STEP_BV<KIND>
    //  (cl (= t bitblast(t)))
    case ProofRule::BV_BITBLAST_STEP:
    {
      Kind k = res[0].getKind();
      // no checking for those yet in Carcara or Isabelle, so we produce holes
      if (k == Kind::BITVECTOR_UDIV || k == Kind::BITVECTOR_UREM
          || k == Kind::BITVECTOR_SHL || k == Kind::BITVECTOR_LSHR
          || k == Kind::BITVECTOR_ASHR)
      {
        return addAletheStep(AletheRule::HOLE,
                             res,
                             nm->mkNode(Kind::SEXPR, d_cl, res),
                             children,
                             {},
                             *cdp);
      }
      // if the term being bitblasted is a variable or a nonbv term, then this
      // is a "bitblast var" step
      auto it = s_bvKindToAletheRule.find(k);
      return addAletheStep(it == s_bvKindToAletheRule.end()
                               ? AletheRule::BV_BITBLAST_STEP_VAR
                               : it->second,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    //================================================= Quantifiers rules
    // ======== Instantiate
    // See proof_rule.h for documentation on the INSTANTIATE rule. This
    // comment uses variable names as introduced there.
    //
    // ----- FORALL_INST, t1 ... tn
    //  VP1
    // ----- OR
    //  VP2              P
    // -------------------- RESOLUTION
    //     (cl F*sigma)^
    //
    // VP1: (cl (or (not (forall ((x1 T1) ... (xn Tn)) F*sigma)
    // VP2: (cl (not (forall ((x1 T1) ... (xn Tn)) F)) F*sigma)
    //
    // ^ the corresponding proof node is F*sigma
    case ProofRule::INSTANTIATE:
    {
      Node vp1 = nm->mkNode(
          Kind::SEXPR, d_cl, nm->mkNode(Kind::OR, children[0].notNode(), res));
      Node vp2 = nm->mkNode(Kind::SEXPR, d_cl, children[0].notNode(), res);
      return addAletheStep(AletheRule::FORALL_INST,
                           vp1,
                           vp1,
                           {},
                           std::vector<Node>{args[0].begin(), args[0].end()},
                           *cdp)
             && addAletheStep(AletheRule::OR, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(Kind::SEXPR, d_cl, res),
                              {vp2, children[0]},
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== Alpha Equivalence
    //
    // Given the formula F = (forall ((y1 A1) ... (yn An)) G) and the
    // substitution sigma = {y1 -> z1, ..., yn -> zn}, the step is represented
    // as
    //
    //  ------------------ refl
    //  (cl (= G G*sigma))
    // -------------------- bind, z1 ... zn (= y1 z1) ... (= yn zn)
    //  (= F F*sigma)
    //
    // In case the sigma is the identity this step is merely converted to
    //
    //  ------------------ refl
    //  (cl (= F F))
    case ProofRule::ALPHA_EQUIV:
    {
      std::vector<Node> varEqs;
      // If y1 ... yn are mapped to y1 ... yn it suffices to use a refl step
      bool allSame = true;
      for (size_t i = 0, size = res[0][0].getNumChildren(); i < size; ++i)
      {
        Node v0 = res[0][0][i], v1 = res[1][0][i];
        allSame = allSame && v0 == v1;
        varEqs.push_back(v0.eqNode(v1));
      }
      if (allSame)
      {
        return addAletheStep(AletheRule::REFL,
                             res,
                             nm->mkNode(Kind::SEXPR, d_cl, res),
                             {},
                             {},
                             *cdp);
      }
      // Reflexivity over the quantified bodies
      Node vp = nm->mkNode(
          Kind::SEXPR, d_cl, nm->mkNode(Kind::EQUAL, res[0][1], res[1][1]));
      addAletheStep(AletheRule::REFL, vp, vp, {}, {}, *cdp);
      // collect variables first
      new_args.insert(new_args.end(), res[1][0].begin(), res[1][0].end());
      new_args.insert(new_args.end(), varEqs.begin(), varEqs.end());
      return addAletheStep(AletheRule::ANCHOR_BIND,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           {vp},
                           new_args,
                           *cdp);
    }
    //================================================= Arithmetic rules
    // ======== Adding Scaled Inequalities
    //
    // -------------------------------------- LA_GENERIC
    // (cl (not P1) ... (not Pn) (>< t1 t2))              P1 ... Pn
    // ------------------------------------------------------------- RESOLUTION
    //  (cl (>< t1 t2))*
    //
    // * the corresponding proof node is (>< t1 t2)
    case ProofRule::ARITH_SUM_UB:
    {
      // if the conclusion were an equality we'd need to phrase LA_GENERIC in
      // terms of disequalities, but ARITH_SUM_UB does not have equalities as
      // conclusions
      Assert(res.getKind() != Kind::EQUAL);
      Node one = nm->mkConstReal(Rational(1));
      Node minusOne = nm->mkConstReal(Rational(-1));
      std::vector<Node> resArgs;
      std::vector<Node> resChildren;
      std::vector<Node> lits{d_cl};
      for (const Node& child : children)
      {
        lits.push_back(child.notNode());
        // equalities are multiplied by minus 1 rather than 1
        new_args.push_back(child.getKind() == Kind::EQUAL ? minusOne : one);
        resArgs.push_back(child);
        resArgs.push_back(d_false);
      }
      lits.push_back(res);
      new_args.push_back(one);
      Node laGen = nm->mkNode(Kind::SEXPR, lits);
      addAletheStep(AletheRule::LA_GENERIC, laGen, laGen, {}, new_args, *cdp);
      resChildren.push_back(laGen);
      resChildren.insert(resChildren.end(), children.begin(), children.end());
      return addAletheStep(AletheRule::RESOLUTION,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           resChildren,
                           d_resPivots ? resArgs : std::vector<Node>(),
                           *cdp);
    }
    // Direct translation
    case ProofRule::ARITH_MULT_POS:
    case ProofRule::ARITH_MULT_NEG:
    {
      return addAletheStep(id == ProofRule::ARITH_MULT_POS
                               ? AletheRule::LA_MULT_POS
                               : AletheRule::LA_MULT_NEG,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Tightening Strict Integer Upper Bounds
    //
    // ----- LA_GENERIC, 1
    //  VP1                      P
    // ------------------------------------- RESOLUTION
    //  (cl (<= i greatestIntLessThan(c)))*
    //
    // VP1: (cl (not (< i c)) (<= i greatestIntLessThan(c)))
    //
    // * the corresponding proof node is (<= i greatestIntLessThan(c))
    case ProofRule::INT_TIGHT_UB:
    {
      Node vp1 = nm->mkNode(Kind::SEXPR, d_cl, children[0].notNode(), res);
      std::vector<Node> new_children = {vp1, children[0]};
      Node one = nm->mkConstReal(Rational(1));
      new_args.push_back(one);
      new_args.push_back(one);
      return addAletheStep(AletheRule::LA_GENERIC, vp1, vp1, {}, new_args, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(Kind::SEXPR, d_cl, res),
                              new_children,
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== Tightening Strict Integer Lower Bounds
    //
    // ----- LA_GENERIC, 1
    //  VP1                      P
    // ------------------------------------- RESOLUTION
    //  (cl (>= i leastIntGreaterThan(c)))*
    //
    // VP1: (cl (not (> i c)) (>= i leastIntGreaterThan(c)))
    //
    // * the corresponding proof node is (>= i leastIntGreaterThan(c))
    case ProofRule::INT_TIGHT_LB:
    {
      Node vp1 = nm->mkNode(Kind::SEXPR, d_cl, children[0].notNode(), res);
      std::vector<Node> new_children = {vp1, children[0]};
      Node one = nm->mkConstReal(Rational(1));
      new_args.push_back(one);
      new_args.push_back(one);
      return addAletheStep(AletheRule::LA_GENERIC, vp1, vp1, {}, new_args, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(Kind::SEXPR, d_cl, res),
                              new_children,
                              d_resPivots
                                  ? std::vector<Node>{children[0], d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
    // ======== Trichotomy of the reals
    //
    // C is always of the format (= x c), (> x c) or (< x c). It has to be
    // concluded from A, B, which are (=> x c), (<= x c), or (not (= x c)). In
    // some cases, rather than (=> x c) we can actually have its negation, i.e.,
    // (not (< x c)), which is accounted for below.
    //
    // The convertion into Alethe is based on la_disequality, which has much
    // the same semantics as ARITH_TRICHOTOMY. The following subproof is
    // common to all the cases (we will refer to it as PI_0):
    //
    // ------------------------------------------------------ la_disequality
    //  (cl (or (= x c) (not (<= x c)) (not (<= c x))))
    // -------------------------------------------------------- or
    //  (cl (= x c) (not (<= x c)) (not (<= c x)))
    //
    // The transformations also use the COMP_SIMPLIFY rule in Alethe, which
    // connects strict and non-strict inequalities. The details for each
    // conversion are given for each case.
    case ProofRule::ARITH_TRICHOTOMY:
    {
      bool success = true;
      Node equal, lesser, greater;
      Kind k = res.getKind();
      Assert(k == Kind::EQUAL || k == Kind::GT || k == Kind::LT)
          << "kind is " << k << "\n";
      Node x = res[0], c = res[1];
      switch (k)
      {
        case Kind::EQUAL:
        {
          Trace("alethe-proof") << "..case EQUAL\n";
          Node leq, geq;
          if (children[0].getKind() == Kind::LEQ)
          {
            leq = children[0];
            geq = children[1];
          }
          else
          {
            leq = children[1];
            geq = children[0];
          }
          Node leqInverted = nm->mkNode(Kind::LEQ, geq[1], geq[0]);
          // The subproof built is (where @p1 is the premise for "geq", @p2 is
          // "leqInverted")
          //
          // PI_1:
          //   with @p0: (= (=> x c) (<= c x))
          //   with @p1: (=> x c)
          //   with @p2: (<= c x)
          //
          // ----- comp_simplify  -------------------equiv_pos2   --- geq
          //  @p0                 (cl (not @p0) (not @p1) @p2)    @p1
          // ---------------------------------------------------- resolution
          //                     @p2
          //
          // Then we combine with the proof PI_0 and use the other premise
          // (for "leq")
          //
          //        --------- leq
          // PI_0    (<= x c)      PI_1
          // --------------------------- resolution
          //        (= x c)
          //
          // where (= x c) is the expected result

          // We first build PI_0:
          Node laDiseqOr = nm->mkNode(
              Kind::SEXPR,
              d_cl,
              nm->mkNode(Kind::OR, res, leq.notNode(), leqInverted.notNode()));
          Node laDiseqCl = nm->mkNode(
              Kind::SEXPR, {d_cl, res, leq.notNode(), leqInverted.notNode()});
          success &=
              addAletheStep(AletheRule::LA_DISEQUALITY,
                            laDiseqOr,
                            laDiseqOr,
                            {},
                            {},
                            *cdp)
              && addAletheStep(
                  AletheRule::OR, laDiseqCl, laDiseqCl, {laDiseqOr}, {}, *cdp);
          // Now we build PI_1:
          Node compSimp = geq.eqNode(leqInverted);
          Node compSimpCl = nm->mkNode(Kind::SEXPR, d_cl, compSimp);
          success &= addAletheStep(
              AletheRule::COMP_SIMPLIFY, compSimpCl, compSimpCl, {}, {}, *cdp);
          Node equivPos2Cl = nm->mkNode(
              Kind::SEXPR,
              {d_cl, compSimp.notNode(), geq.notNode(), leqInverted});
          success &= addAletheStep(
              AletheRule::EQUIV_POS2, equivPos2Cl, equivPos2Cl, {}, {}, *cdp);
          Node resPi1Conc = nm->mkNode(Kind::SEXPR, d_cl, leqInverted);
          success &= addAletheStep(
              AletheRule::RESOLUTION,
              resPi1Conc,
              resPi1Conc,
              {compSimpCl, equivPos2Cl, geq},
              d_resPivots ? std::vector<Node>{compSimp, d_true, geq, d_false}
                          : std::vector<Node>(),
              *cdp);
          // Now we build the final resultion
          success &= addAletheStep(
              AletheRule::RESOLUTION,
              res,
              nm->mkNode(Kind::SEXPR, d_cl, res),
              {leq, laDiseqCl, resPi1Conc},
              d_resPivots ? std::vector<Node>{leq, d_true, leqInverted, d_false}
                          : std::vector<Node>(),
              *cdp);
          break;
        }
        case Kind::GT:
        {
          Trace("alethe-proof") << "..case GT\n";
          Node geq, notEq;
          Kind kc0 = children[0].getKind();
          if (kc0 == Kind::GEQ
              || (kc0 == Kind::NOT && children[0][0].getKind() == Kind::LT))
          {
            geq = children[0];
            notEq = children[1];
          }
          else
          {
            geq = children[1];
            notEq = children[0];
          }
          Node leq = nm->mkNode(Kind::LEQ, x, c);
          Node leqInverted = nm->mkNode(Kind::LEQ, c, x);
          Assert(notEq.getKind() == Kind::NOT
                 && notEq[0].getKind() == Kind::EQUAL);
          // it may be that the premise supposed to be (>= x c) is actually the
          // literal (not (< x c)). In this case we use that premise to deriv
          // (>= x c), so that the reconstruction below remains the same
          if (geq.getKind() != Kind::GEQ)
          {
            Assert(geq.getKind() == Kind::NOT && geq[0].getKind() == Kind::LT);
            Node notLt = geq;
            geq = nm->mkNode(Kind::GEQ, x, c);
            //  @pa: (= (< x c) (not (<= c x)))
            //  @pb: (< x c)
            //  @pc: (<= c x)
            //  notLT : (not @pb)
            //
            // PI_a:
            //
            // --- comp_simplify --------------------- equiv_pos1    ----- notLT
            // @pa               (cl (not @pa) @pb (not (not @pc)))  (not @pb)
            // ------------------------------------------------------ resolution
            //              (cl (not (not @pc)))
            //
            //
            // PI_b:
            //
            //  ------------------------------ NOT_NOT -------------------- PI_a
            //  (cl (not (not (not @pc))) @pc)         (cl (not (not @pc)))
            // ------------------------------------------------------ resolution
            //                             @pc
            //
            // PI_c:
            //
            //  @pd: (= (>= x c) (<= c x))
            //
            // --- comp_simplify -------------------------- equiv_pos1  --- PI_b
            // @pd               (cl (not @pd) (>= x c) (not @pc))      @pc
            // ------------------------------------------------------ resolution
            //              (cl (>= x c))
            //
            Node pb = notLt[0];
            Node pc = leqInverted;
            Node pa = pb.eqNode(pc.notNode());
            // We first build PI_a:
            Node compSimpCl = nm->mkNode(Kind::SEXPR, d_cl, pa);
            success &= addAletheStep(AletheRule::COMP_SIMPLIFY,
                                     compSimpCl,
                                     compSimpCl,
                                     {},
                                     {},
                                     *cdp);
            Node equivPos1Cl = nm->mkNode(
                Kind::SEXPR, {d_cl, pa.notNode(), pb, pc.notNode().notNode()});
            success &= addAletheStep(
                AletheRule::EQUIV_POS1, equivPos1Cl, equivPos1Cl, {}, {}, *cdp);
            Node resPiAConc =
                nm->mkNode(Kind::SEXPR, d_cl, pc.notNode().notNode());
            success &= addAletheStep(
                AletheRule::RESOLUTION,
                resPiAConc,
                resPiAConc,
                {compSimpCl, equivPos1Cl, pb.notNode()},
                d_resPivots ? std::vector<Node>{pa, d_true, pb, d_true}
                            : std::vector<Node>(),
                *cdp);
            // We then build PI_b:
            Node notNot = pc.notNode().notNode().notNode();
            Node notNotCl =
                nm->mkNode(Kind::SEXPR, d_cl, pc.notNode().notNode().notNode());
            success &= addAletheStep(
                AletheRule::NOT_NOT, notNotCl, notNotCl, {}, {}, *cdp);
            Node resPiBConc =
                nm->mkNode(Kind::SEXPR, d_cl, pc.notNode().notNode());
            success &= addAletheStep(
                AletheRule::RESOLUTION,
                resPiBConc,
                resPiBConc,
                {notNotCl, resPiAConc},
                d_resPivots ? std::vector<Node>{pc.notNode().notNode(), d_false}
                            : std::vector<Node>(),
                *cdp);
            // Now we conclude, building PI_c
            Node pd = geq.eqNode(pc);
            compSimpCl = nm->mkNode(Kind::SEXPR, d_cl, pd);
            success &= addAletheStep(AletheRule::COMP_SIMPLIFY,
                                     compSimpCl,
                                     compSimpCl,
                                     {},
                                     {},
                                     *cdp);
            equivPos1Cl = nm->mkNode(Kind::SEXPR,
                                     {d_cl, pd.notNode(), geq, pc.notNode()});
            success &= addAletheStep(
                AletheRule::EQUIV_POS1, equivPos1Cl, equivPos1Cl, {}, {}, *cdp);
            success &= addAletheStep(
                AletheRule::RESOLUTION,
                geq,
                nm->mkNode(Kind::SEXPR, d_cl, geq),
                {compSimpCl, equivPos1Cl, resPiBConc},
                d_resPivots ? std::vector<Node>{pd, d_true, pc, d_false}
                            : std::vector<Node>(),
                *cdp);
          }
          // The subproof built here uses the PI_1 defined in the case above,
          // where the premise for "geq" is used to conclude leqInverted. Here
          // @p4 is "res", @p5 is "leq". The goal of PI_2 is to conclude (not
          // (not @p5)), which can remove the element from the conclusion of
          // PI_0 that is (not @p5). The conclusion of PI_1 and notEq exclude
          // the other elements, such that only @p4 will remain, the expected
          // conclusion.
          //
          // PI_2:
          //   with @p3: (= (> x c) (not (<= x c)))
          //   with @p4: (> x c)
          //   with @p5: (<= x c)
          //
          // ----- comp_simplify  ----------------------------------- equiv_pos1
          //  @p3                 (cl (not @p3) @p4 (not (not @p5)))
          // ------------------------------------------------------- resolution
          //              (cl @p4 (not (not @p5)))
          //
          // Then we combine the proofs PI_0, the premise for "notEq", and
          // PI_1 and PI_2:
          //
          //        --------- notEq
          // PI_0   (not (= x c))    PI_1    PI_2
          // ------------------------------------- resolution
          //        (> x c)
          //
          // where (= x c) is the expected result

          // We first build PI_0:
          Node laDiseqOr = nm->mkNode(
              Kind::SEXPR,
              d_cl,
              nm->mkNode(
                  Kind::OR, notEq[0], leq.notNode(), leqInverted.notNode()));
          Node laDiseqCl = nm->mkNode(
              Kind::SEXPR,
              {d_cl, notEq[0], leq.notNode(), leqInverted.notNode()});
          success &=
              addAletheStep(AletheRule::LA_DISEQUALITY,
                            laDiseqOr,
                            laDiseqOr,
                            {},
                            {},
                            *cdp)
              && addAletheStep(
                  AletheRule::OR, laDiseqCl, laDiseqCl, {laDiseqOr}, {}, *cdp);
          // Now we build PI_1:
          Node compSimp = geq.eqNode(leqInverted);
          Node compSimpCl = nm->mkNode(Kind::SEXPR, d_cl, compSimp);
          success &= addAletheStep(
              AletheRule::COMP_SIMPLIFY, compSimpCl, compSimpCl, {}, {}, *cdp);
          Node equivPos2Cl = nm->mkNode(
              Kind::SEXPR,
              {d_cl, compSimp.notNode(), geq.notNode(), leqInverted});
          success &= addAletheStep(
              AletheRule::EQUIV_POS2, equivPos2Cl, equivPos2Cl, {}, {}, *cdp);
          Node resPi1Conc = nm->mkNode(Kind::SEXPR, d_cl, leqInverted);
          success &= addAletheStep(
              AletheRule::RESOLUTION,
              resPi1Conc,
              resPi1Conc,
              {compSimpCl, equivPos2Cl, geq},
              d_resPivots ? std::vector<Node>{compSimp, d_true, geq, d_false}
                          : std::vector<Node>(),
              *cdp);
          // Now we build PI_2
          Node compSimp2 = res.eqNode(leq.notNode());
          Node compSimp2Cl = nm->mkNode(Kind::SEXPR, d_cl, compSimp2);
          success &= addAletheStep(AletheRule::COMP_SIMPLIFY,
                                   compSimp2Cl,
                                   compSimp2Cl,
                                   {},
                                   {},
                                   *cdp);
          Node equivPos1Cl = nm->mkNode(
              Kind::SEXPR,
              {d_cl, compSimp2.notNode(), res, leq.notNode().notNode()});
          success &= addAletheStep(
              AletheRule::EQUIV_POS1, equivPos1Cl, equivPos1Cl, {}, {}, *cdp);
          Node resPi2Conc =
              nm->mkNode(Kind::SEXPR, d_cl, res, leq.notNode().notNode());
          success &=
              addAletheStep(AletheRule::RESOLUTION,
                            resPi2Conc,
                            resPi2Conc,
                            {compSimp2Cl, equivPos1Cl},
                            d_resPivots ? std::vector<Node>{compSimp2, d_true}
                                        : std::vector<Node>(),
                            *cdp);
          // Now we build the final resolution
          success &=
              addAletheStep(AletheRule::RESOLUTION,
                            res,
                            nm->mkNode(Kind::SEXPR, d_cl, res),
                            {notEq, laDiseqCl, resPi1Conc, resPi2Conc},
                            d_resPivots ? std::vector<Node>{notEq[0],
                                                            d_false,
                                                            leqInverted,
                                                            d_false,
                                                            leq.notNode(),
                                                            d_true}
                                        : std::vector<Node>(),
                            *cdp);
          break;
        }
        case Kind::LT:
        {
          Trace("alethe-proof") << "..case LT\n";
          Node leq, notEq;
          Kind kc0 = children[0].getKind();
          if (kc0 == Kind::LEQ
              || (kc0 == Kind::NOT && children[0][0].getKind() == Kind::LT))
          {
            leq = children[0];
            notEq = children[1];
          }
          else
          {
            leq = children[1];
            notEq = children[0];
          }
          Assert(notEq.getKind() == Kind::NOT
                 && notEq[0].getKind() == Kind::EQUAL);
          Assert(leq.getKind() == Kind::LEQ);
          Node leqInverted = nm->mkNode(Kind::LEQ, c, x);
          // The subproof built here uses the PI_0 defined in the case
          // above. Note that @p7 is res and @p8 is leqInverted.
          //
          // PI_3:
          //   with @p6: (= (< x c) (not (<= c x)))
          //   with @p7: (< x c)
          //   with @p8: (<= c x)
          //
          // ----- comp_simplify  ----------------------------------- equiv_pos1
          //  @p6                  (cl (not @p6) @p7 (not (not @p8)))
          // -------------------------------------------------------- resolution
          //              (cl @p7 (not (not @p8)))
          //
          // Then we combine the proofs PI_0, the premise for "notEq", the
          // premise for "leq", and PI_3 above:
          //
          //        ------- notEq  -----leq  ---------------------------- PI_3
          // PI_0   (not (= x c))  (<= x c)  (cl (< x c) (not (not (<= c x))))
          // -------------------------------------------------------- resolution
          //                      (< x c)
          //
          // where (< x c) is the expected result

          // We first build PI_0:
          Node laDiseqOr = nm->mkNode(
              Kind::SEXPR,
              d_cl,
              nm->mkNode(
                  Kind::OR, notEq[0], leq.notNode(), leqInverted.notNode()));
          Node laDiseqCl = nm->mkNode(
              Kind::SEXPR,
              {d_cl, notEq[0], leq.notNode(), leqInverted.notNode()});
          success &=
              addAletheStep(AletheRule::LA_DISEQUALITY,
                            laDiseqOr,
                            laDiseqOr,
                            {},
                            {},
                            *cdp)
              && addAletheStep(
                  AletheRule::OR, laDiseqCl, laDiseqCl, {laDiseqOr}, {}, *cdp);
          // Now we build PI_3:
          Node compSimp = res.eqNode(leqInverted.notNode());
          Node compSimpCl = nm->mkNode(Kind::SEXPR, d_cl, compSimp);
          success &= addAletheStep(
              AletheRule::COMP_SIMPLIFY, compSimpCl, compSimpCl, {}, {}, *cdp);
          Node equivPos1Cl = nm->mkNode(
              Kind::SEXPR,
              {d_cl, compSimp.notNode(), res, leqInverted.notNode().notNode()});
          success &= addAletheStep(
              AletheRule::EQUIV_POS1, equivPos1Cl, equivPos1Cl, {}, {}, *cdp);
          // We do a single resolution step , inlining the one finishing PI_3
          // above, to build the final resolution
          success &= addAletheStep(
              AletheRule::RESOLUTION,
              res,
              nm->mkNode(Kind::SEXPR, d_cl, res),
              {laDiseqCl, notEq, leq, equivPos1Cl, compSimpCl},
              d_resPivots ? std::vector<Node>{notEq[0],
                                              d_true,
                                              leq,
                                              d_false,
                                              leqInverted.notNode(),
                                              d_true,
                                              compSimp,
                                              d_false}
                          : std::vector<Node>(),
              *cdp);
          break;
        }
        default:
        {
          Unreachable() << "should not have gotten here";
        }
      }
      return success;
    }
    default:
    {
      Trace("alethe-proof")
          << "... rule not translated yet " << id << " / " << res << " "
          << children << " " << args << std::endl;
      std::stringstream ss;
      ss << "\"" << id << "\"";
      std::vector<Node> newArgs{nm->mkRawSymbol(ss.str(), nm->sExprType())};
      newArgs.insert(newArgs.end(), args.begin(), args.end());
      return addAletheStep(AletheRule::HOLE,
                           res,
                           nm->mkNode(Kind::SEXPR, d_cl, res),
                           children,
                           newArgs,
                           *cdp);
    }
  }
  Trace("alethe-proof") << "... error translating rule " << id << " / " << res
                        << " " << children << " " << args << std::endl;
  return false;
}

bool AletheProofPostprocessCallback::maybeReplacePremiseProof(Node premise,
                                                              CDProof* cdp)
{
  // Test if the proof of premise concludes a non-singleton clause. Assumptions
  // always succeed the test.
  std::shared_ptr<ProofNode> premisePf = cdp->getProofFor(premise);
  if (premisePf->getRule() == ProofRule::ASSUME)
  {
    return false;
  }
  Node premisePfConclusion = premisePf->getArguments()[2];
  // not a proof of a non-singleton clause
  if (premisePfConclusion.getNumChildren() <= 2
      || premisePfConclusion[0] != d_cl)
  {
    return false;
  }
  // If this resolution child is used as a singleton OR but the rule
  // justifying it concludes a clause, then we are often in this scenario:
  //
  // (or t1 ... tn)
  // -------------- OR
  // (cl t1 ... tn)
  // ---------------- FACTORING/REORDERING
  // (cl t1' ... tn')
  //
  // where what is used in the resolution is actually (or t1' ... tn').
  //
  // This happens when (or t1' ... tn') has been added to the SAT solver as
  // a literal as well, and its node clashed with the conclusion of the
  // FACTORING/REORDERING step.
  //
  // When this is happening at one level, as in the example above, a solution is
  // to *not* use FACTORING/REORDERING (which in Alethe operate on clauses) but
  // generate a proof to obtain the expected node (or t1' ...  tn') from the
  // original node (or t1 ... tn).
  //
  // If the change is due to FACTORING, this can be easily obtained via
  // rewriting (with OR_SIMPLIFY), equivalence elimination, and resolution.
  //
  // Otherise we are either in the case of REORDERING or in a case where we
  // cannot easily access a proof of (or t1 ... tn). In both case we will derive
  // (cl (or t1' ... tn')) using n or_neg steps, as shown below.
  NodeManager* nm = nodeManager();
  Trace("alethe-proof") << "\n";
  AletheRule premiseProofRule = getAletheRule(premisePf->getArguments()[0]);
  if (premiseProofRule == AletheRule::CONTRACTION
      && getAletheRule(premisePf->getChildren()[0]->getArguments()[0])
             == AletheRule::OR)
  {
    // get great grand child
    std::shared_ptr<ProofNode> premiseChildPf =
        premisePf->getChildren()[0]->getChildren()[0];
    Node premiseChildConclusion = premiseChildPf->getResult();
    // Note that we need to add this proof node explicitly to cdp because it
    // does not have a step for premiseChildConclusion. Rather it is only
    // present in cdp as a descendant of premisePf (which is in cdp), so if
    // premisePf is to be lost, then so will premiseChildPf. By adding
    // premiseChildPf explicitly, it can be retrieved to justify
    // premiseChildConclusion when requested.
    cdp->addProof(premiseChildPf);
    // equate it to what we expect. If the premise rule is CONTRACTION, we can
    // justify it via OR_SIMPLIFY. Otherwise...
    Node equiv = premiseChildConclusion.eqNode(premise);
    bool success = true;
    if (premiseProofRule == AletheRule::CONTRACTION)
    {
      success &= addAletheStep(AletheRule::OR_SIMPLIFY,
                               equiv,
                               nm->mkNode(Kind::SEXPR, d_cl, equiv),
                               {},
                               {},
                               *cdp);
      Node equivElim = nm->mkNode(
          Kind::SEXPR,
          {d_cl, equiv.notNode(), premiseChildConclusion.notNode(), premise});
      success &= addAletheStep(
          AletheRule::EQUIV_POS2, equivElim, equivElim, {}, {}, *cdp);
      Node newPremise = nm->mkNode(Kind::SEXPR, d_cl, premise);
      Trace("alethe-proof")
          << "Reverted handling as a clause for converting "
          << premiseChildConclusion << " into " << premise << std::endl;
      return success
             && addAletheStep(AletheRule::RESOLUTION,
                              newPremise,
                              newPremise,
                              {equivElim, equiv, premiseChildConclusion},
                              d_resPivots
                                  ? std::vector<Node>{equiv,
                                                      d_false,
                                                      premiseChildConclusion,
                                                      d_false}
                                  : std::vector<Node>(),
                              *cdp);
    }
  }
  // Derive (cl (or t1' ... tn')) from (cl t1' ... tn') (i.e., the premise) with
  //
  //             -----------------------  ...  --------------------- or_neg
  //   premise   (cl premise, (not t1'))  ...  (cl premise, (not tn'))
  //  ---------------------------- resolution
  //  (cl premise ... premise)
  //  ---------------------------- contraction
  //         (cl premise)
  std::vector<Node> resPremises{premise};
  std::vector<Node> resArgs;
  std::vector<Node> contractionPremiseChildren{d_cl};
  bool success = true;

  for (size_t i = 0, size = premise.getNumChildren(); i < size; ++i)
  {
    Node nNeg = premise[i].notNode();
    resPremises.push_back(nm->mkNode(Kind::SEXPR, d_cl, premise, nNeg));
    success &= addAletheStep(AletheRule::OR_NEG,
                             resPremises.back(),
                             resPremises.back(),
                             {},
                             std::vector<Node>{nm->mkConstInt(i)},
                             *cdp);
    resArgs.push_back(nNeg[0]);
    resArgs.push_back(d_true);
    contractionPremiseChildren.push_back(premise);
  }
  Node contractionPremise = nm->mkNode(Kind::SEXPR, contractionPremiseChildren);
  success &= addAletheStep(AletheRule::RESOLUTION,
                           contractionPremise,
                           contractionPremise,
                           resPremises,
                           d_resPivots ? resArgs : std::vector<Node>(),
                           *cdp);
  Node newPremise = nm->mkNode(Kind::SEXPR, d_cl, premise);
  return success
         && addAletheStep(AletheRule::CONTRACTION,
                          newPremise,
                          newPremise,
                          {contractionPremise},
                          {},
                          *cdp);
}

bool AletheProofPostprocessCallback::updatePost(
    Node res,
    ProofRule id,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp)
{
  NodeManager* nm = nodeManager();
  AletheRule rule = getAletheRule(args[0]);
  Trace("alethe-proof") << "...Alethe post-update " << rule << " / " << res
                        << " / args: " << args << std::endl;
  bool success = true;
  switch (rule)
  {
    // In the case of a resolution rule, the rule might originally have been a
    // cvc5 RESOLUTION or CHAIN_RESOLUTION rule, and it is possible that one of
    // the children was printed as (cl (or F1 ... Fn)) but it was actually used
    // as (cl F1 ... Fn). However, from the pivot of the resolution step for the
    // child we can determine if an additional OR step is necessary to convert
    // the clase (cl (or ...)) to (cl ...). This is done below.
    case AletheRule::RESOLUTION_OR:
    {
      // We need pivots to more easily do the computations here, so we require
      // them.
      Assert(args.size() >= 4);
      std::vector<Node> newChildren = children;
      bool hasUpdated = false;

      // Note that we will have inverted the order of polarity/pivot.
      size_t polIdx, pivIdx;
      // their starting positions in the arguments
      polIdx = 4;
      pivIdx = 3;
      // The first child is used as a non-singleton clause if it is not equal
      // to its pivot L_1. Since it's the first clause in the resolution it can
      // only be equal to the pivot in the case the polarity is true.
      if (children[0].getKind() == Kind::OR
          && (args[polIdx] != d_true || args[pivIdx] != children[0]))
      {
        std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[0]);
        bool childPfIsAssume = childPf->getRule() == ProofRule::ASSUME;
        Node childConclusion =
            childPfIsAssume ? childPf->getResult() : childPf->getArguments()[2];
        // if child conclusion is of the form (sexpr cl (or ...)), then we need
        // to add an OR step, since this child must not be a singleton
        if ((childPfIsAssume && childConclusion.getKind() == Kind::OR)
            || (childConclusion.getNumChildren() == 2
                && childConclusion[0] == d_cl
                && childConclusion[1].getKind() == Kind::OR))
        {
          hasUpdated = true;
          // Add or step
          std::vector<Node> subterms{d_cl};
          if (childPfIsAssume)
          {
            subterms.insert(
                subterms.end(), childConclusion.begin(), childConclusion.end());
          }
          else
          {
            subterms.insert(subterms.end(),
                            childConclusion[1].begin(),
                            childConclusion[1].end());
          }
          Node newConclusion = nm->mkNode(Kind::SEXPR, subterms);
          success &= addAletheStep(AletheRule::OR,
                                   newConclusion,
                                   newConclusion,
                                   {children[0]},
                                   {},
                                   *cdp);
          newChildren[0] = newConclusion;
          Trace("alethe-proof") << "Added OR step for " << childConclusion
                                << " / " << newConclusion << std::endl;
        }
      }
      // The premise is used a singleton clause. We must guarantee that its
      // proof indeed concludes a singleton clause.
      else if (children[0].getKind() == Kind::OR)
      {
        Assert(args[polIdx] == d_true && args[pivIdx] == children[0]);
        if (maybeReplacePremiseProof(children[0], cdp))
        {
          hasUpdated = true;
          newChildren[0] = nm->mkNode(Kind::SEXPR, d_cl, children[0]);
        }
      }
      // For all other children C_i the procedure is similar. There is however a
      // key difference in the choice of the pivot element which is now the
      // L_{i-1}, i.e. the pivot of the child with the result of the i-1
      // resolution steps between the children before it. Therefore, if the
      // policy id_{i-1} is true, the pivot has to appear negated in the child
      // in which case it should not be a (cl (or F1 ... Fn)) node. The same is
      // true if it isn't the pivot element.
      for (std::size_t i = 1, size = children.size(); i < size; ++i)
      {
        polIdx = 2 * (i - 1) + 3 + 1;
        pivIdx = 2 * (i - 1) + 3;
        if (children[i].getKind() == Kind::OR
            && (args[polIdx] != d_false
                || d_anc.convert(args[pivIdx]) != d_anc.convert(children[i])))
        {
          if (args[polIdx] == d_false
              && d_anc.convert(args[pivIdx]) == d_anc.convert(children[i]))
          {
            continue;
          }
          std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[i]);
          bool childPfIsAssume = childPf->getRule() == ProofRule::ASSUME;
          Node childConclusion = childPfIsAssume ? childPf->getResult()
                                                 : childPf->getArguments()[2];
          // Add or step
          if ((childPfIsAssume && childConclusion.getKind() == Kind::OR)
              || (childConclusion.getNumChildren() == 2
                  && childConclusion[0] == d_cl
                  && childConclusion[1].getKind() == Kind::OR))
          {
            hasUpdated = true;
            std::vector<Node> lits{d_cl};
            if (childPfIsAssume)
            {
              lits.insert(
                  lits.end(), childConclusion.begin(), childConclusion.end());
            }
            else
            {
              lits.insert(lits.end(),
                          childConclusion[1].begin(),
                          childConclusion[1].end());
            }
            Node conclusion = nm->mkNode(Kind::SEXPR, lits);
            success &= addAletheStep(AletheRule::OR,
                                     conclusion,
                                     conclusion,
                                     {children[i]},
                                     {},
                                     *cdp);
            newChildren[i] = conclusion;
            Trace("alethe-proof") << "Added OR step for " << childConclusion
                                  << " / " << conclusion << std::endl;
          }
        }
        // As for the first premise, we need to handle the case in which the
        // premise is a singleton but the rule concluding it yields a clause.
        else if (children[i].getKind() == Kind::OR)
        {
          Assert(args[polIdx] == d_false
                 && d_anc.convert(args[pivIdx]) == d_anc.convert(children[i]));
          if (maybeReplacePremiseProof(children[i], cdp))
          {
            hasUpdated = true;
            newChildren[i] = nm->mkNode(Kind::SEXPR, d_cl, children[i]);
          }
        }
      }
      if (TraceIsOn("alethe-proof"))
      {
        if (hasUpdated)
        {
          Trace("alethe-proof")
              << "... update alethe step in finalizer " << res << " "
              << newChildren << " / " << args << std::endl;
        }
        else
        {
          Trace("alethe-proof") << "... no update\n";
        }
      }
      success &= addAletheStep(
          AletheRule::RESOLUTION,
          res,
          args[2],
          newChildren,
          d_resPivots ? std::vector<Node>{args.begin() + 3, args.end()}
                      : std::vector<Node>{},
          *cdp);
      return success;
    }
    // A application of the FACTORING rule:
    //
    // (or a a b)
    // ---------- FACTORING
    //  (or a b)
    //
    // might be translated during pre-visit (update) to:
    //
    // (or (cl a a b))*
    // ---------------- CONTRACTION
    //  (cl a b)**
    //
    // In this post-visit an additional OR step is added in that case:
    //
    // (cl (or a a b))*
    // ---------------- OR
    // (cl a a b)
    // ---------------- CONTRACTION
    // (cl a b)**
    //
    // * the corresponding proof node is (or a a b)
    // ** the corresponding proof node is (or a b)
    //
    // The process is analogous for REORDERING.
    case AletheRule::REORDERING:
    case AletheRule::CONTRACTION:
    {
      std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[0]);
      bool childPfIsAssume = childPf->getRule() == ProofRule::ASSUME;
      Node childConclusion =
          childPfIsAssume ? childPf->getResult() : childPf->getArguments()[2];
      if ((childPfIsAssume && childConclusion.getKind() == Kind::OR)
          || (childConclusion.getNumChildren() == 2
              && childConclusion[0] == d_cl
              && childConclusion[1].getKind() == Kind::OR))
      {
        // Add or step for child
        std::vector<Node> subterms{d_cl};
        if (childPfIsAssume)
        {
          subterms.insert(
              subterms.end(), childConclusion.begin(), childConclusion.end());
        }
        else
        {
          subterms.insert(subterms.end(),
                          childConclusion[1].begin(),
                          childConclusion[1].end());
        }
        Node newChild = nm->mkNode(Kind::SEXPR, subterms);
        success &= addAletheStep(
            AletheRule::OR, newChild, newChild, {children[0]}, {}, *cdp);
        Trace("alethe-proof")
            << "Added OR step in finalizer to child " << childConclusion
            << " / " << newChild << std::endl;
        // update res step
        cdp->addStep(res, ProofRule::ALETHE_RULE, {newChild}, args);
        return success;
      }
      Trace("alethe-proof") << "... no update\n";
      return false;
    }
    default:
    {
      Trace("alethe-proof") << "... no update\n";
      return false;
    }
  }
  Trace("alethe-proof") << "... no update\n";
  return false;
}

bool AletheProofPostprocessCallback::ensureFinalStep(
    Node res,
    ProofRule id,
    std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp)
{
  bool success = true;
  NodeManager* nm = nodeManager();
  std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[0]);

  // convert inner proof, i.e., children[0], if its conclusion is (cl false) or
  // if it's a false assumption
  //
  //   ...
  // -------------------    ---------------------- false
  //  (cl false)             (cl (not false))
  // -------------------------------------------------- resolution
  //                       (cl)
  if ((childPf->getRule() == ProofRule::ALETHE_RULE
       && childPf->getArguments()[2].getNumChildren() == 2
       && childPf->getArguments()[2][1] == d_false)
      || (childPf->getRule() == ProofRule::ASSUME
          && childPf->getResult() == d_false))
  {
    Node notFalse =
        nm->mkNode(Kind::SEXPR, d_cl, d_false.notNode());  // (cl (not false))
    Node newChild = nm->mkNode(Kind::SEXPR, d_cl);         // (cl)

    success &=
        addAletheStep(AletheRule::FALSE, notFalse, notFalse, {}, {}, *cdp);
    success &= addAletheStep(
        AletheRule::RESOLUTION,
        newChild,
        newChild,
        {children[0], notFalse},
        d_resPivots ? std::vector<Node>{d_false, d_true} : std::vector<Node>(),
        *cdp);
    children[0] = newChild;
  }

  // Sanitize original assumptions and create a double scope to hold them, where
  // the first scope is empty. This is needed because of the expected form a
  // proof node to be printed.
  std::vector<Node> sanitizedArgs;
  for (const Node& a : args)
  {
    Node conv = d_anc.maybeConvert(a, true);
    if (conv.isNull())
    {
      d_reasonForConversionFailure = d_anc.getError();
      success = false;
      break;
    }
    // avoid repeated assumptions
    if (std::find(sanitizedArgs.begin(), sanitizedArgs.end(), conv)
        == sanitizedArgs.end())
    {
      sanitizedArgs.push_back(conv);
    }
  }
  Node placeHolder = nm->mkNode(Kind::SEXPR, res);
  cdp->addStep(placeHolder, ProofRule::SCOPE, children, sanitizedArgs);
  return success && cdp->addStep(res, ProofRule::SCOPE, {placeHolder}, {});
}

bool AletheProofPostprocessCallback::addAletheStep(
    AletheRule rule,
    Node res,
    Node conclusion,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> newArgs{
      nodeManager()->mkConstInt(Rational(static_cast<uint32_t>(rule)))};
  newArgs.push_back(res);
  conclusion = d_anc.maybeConvert(conclusion);
  if (conclusion.isNull())
  {
    d_reasonForConversionFailure = d_anc.getError();
    return false;
  }
  newArgs.push_back(conclusion);
  for (const Node& arg : args)
  {
    Node conv = d_anc.maybeConvert(arg);
    if (conv.isNull())
    {
      d_reasonForConversionFailure = d_anc.getError();
      return false;
    }
    newArgs.push_back(conv);
  }
  Trace("alethe-proof") << "... add alethe step " << res << " / " << conclusion
                        << " " << rule << " " << children << " / " << newArgs
                        << std::endl;
  return cdp.addStep(res, ProofRule::ALETHE_RULE, children, newArgs);
}

bool AletheProofPostprocessCallback::addAletheStepFromOr(
    AletheRule rule,
    Node res,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  Assert(res.getKind() == Kind::OR);
  std::vector<Node> subterms = {d_cl};
  subterms.insert(subterms.end(), res.begin(), res.end());
  Node conclusion = nodeManager()->mkNode(Kind::SEXPR, subterms);
  return addAletheStep(rule, res, conclusion, children, args, cdp);
}

AletheProofPostprocess::AletheProofPostprocess(Env& env,
                                               AletheNodeConverter& anc)
    : EnvObj(env), d_cb(env, anc, options().proof.proofAletheResPivots)
{
}

AletheProofPostprocess::~AletheProofPostprocess() {}

const std::string& AletheProofPostprocess::getError()
{
  return d_reasonForConversionFailure;
}

bool AletheProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  if (logicInfo().isHigherOrder())
  {
    std::stringstream ss;
    ss << "\"Proof unsupported by Alethe: contains higher-order elements\"";
    d_reasonForConversionFailure = ss.str();
    return false;
  }
  // first two nodes are scopes for definitions and other assumptions. We
  // process only the internal proof node. And we merge these two scopes
  Assert(pf->getRule() == ProofRule::SCOPE
         && pf->getChildren()[0]->getRule() == ProofRule::SCOPE);
  std::shared_ptr<ProofNode> definitionsScope = pf;
  std::shared_ptr<ProofNode> assumptionsScope = pf->getChildren()[0];
  std::shared_ptr<ProofNode> internalProof = assumptionsScope->getChildren()[0];
  // Translate proof node
  ProofNodeUpdater updater(d_env, d_cb, false, false);
  updater.process(internalProof);
  if (d_reasonForConversionFailure.empty())
  {
    // In the Alethe proof format the final step has to be (cl). However, after
    // the translation, the final step might still be (cl false). In that case
    // additional steps are required.  The function has the additional purpose
    // of sanitizing the arguments of the outer SCOPEs
    CDProof cpf(d_env,
                nullptr,
                "AletheProofPostProcess::ensureFinalStep::CDProof",
                true);
    std::vector<Node> ccn{internalProof->getResult()};
    cpf.addProof(internalProof);
    std::vector<Node> args{definitionsScope->getArguments().begin(),
                           definitionsScope->getArguments().end()};
    args.insert(args.end(),
                assumptionsScope->getArguments().begin(),
                assumptionsScope->getArguments().end());
    if (d_cb.ensureFinalStep(
            definitionsScope->getResult(), ProofRule::SCOPE, ccn, args, &cpf))
    {
      std::shared_ptr<ProofNode> npn =
          cpf.getProofFor(definitionsScope->getResult());

      // then, update the original proof node based on this one
      Trace("pf-process-debug") << "Update node..." << std::endl;
      d_env.getProofNodeManager()->updateNode(pf.get(), npn.get());
      Trace("pf-process-debug") << "...update node finished." << std::endl;
    }
  }
  // Since the final step may also lead to issues, need to test here again
  if (!d_cb.getError().empty())
  {
    d_reasonForConversionFailure = d_cb.getError();
    return false;
  }
  return true;
}

}  // namespace proof
}  // namespace cvc5::internal
