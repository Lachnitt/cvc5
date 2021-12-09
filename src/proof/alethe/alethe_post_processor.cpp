/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing proof nodes into Alethe proof nodes
 */

#include "proof/alethe/alethe_post_processor.h"

#include <bits/c++config.h>

#include <sstream>

#include "base/configuration.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/proof_options.h"
#include "proof/alethe/alethe_proof_rule.h"
#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "rewriter/rewrite_proof_rule.h"
#include "theory/builtin/proof_checker.h"
#include "util/rational.h"

using namespace cvc5::kind;

namespace cvc5 {

namespace proof {

AletheProofPostprocessCallback::AletheProofPostprocessCallback(
    ProofNodeManager* pnm, AletheNodeConverter& anc)
    : d_pnm(pnm), d_anc(anc)
{
  NodeManager* nm = NodeManager::currentNM();
  d_cl = nm->mkBoundVar("cl", nm->sExprType());
}

bool AletheProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                  const std::vector<Node>& fa,
                                                  bool& continueUpdate)
{
  return pn->getRule() != PfRule::ALETHE_RULE;
}

bool AletheProofPostprocessCallback::update(Node res,
                                            PfRule id,
                                            const std::vector<Node>& children,
                                            const std::vector<Node>& args,
                                            CDProof* cdp,
                                            bool& continueUpdate)
{
  Trace("alethe-proof") << "- Alethe post process callback " << res << " " << id
                        << " " << children << " / " << args << std::endl;

  NodeManager* nm = NodeManager::currentNM();
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
    // that is then printed as (cl (or b c)). We denote this wrapping of a proof
    // node by using an extra pair of parenthesis, i.e. ((or b c)) is the proof
    // node printed as (cl (or b c)).
    //
    // Adding an OR node to a premises will take place in the finalize function
    // where in the case that a step is printed as (cl (or F1 ... Fn)) but used
    // as (cl F1 ... Fn) an OR step is added to transform it to this very thing.
    // This is necessary for rules that work on clauses, i.e. RESOLUTION,
    // CHAIN_RESOLUTION, REORDERING and FACTORING.
    //
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
    //================================================= Core rules
    //======================== Assume and Scope
    case PfRule::ASSUME:
    {
      return addAletheStep(AletheRule::ASSUME, res, res, children, {}, *cdp);
    }
    // See proof_rule.h for documentation on the SCOPE rule. This comment uses
    // variable names as introduced there. Since the SCOPE rule originally
    // concludes
    // (=> (and F1 ... Fn) F) or (not (and F1 ... Fn)) but the ANCHOR rule
    // concludes (cl (not F1) ... (not Fn) F), to keep the original shape of the
    // proof node it is necessary to rederive the original conclusion. The
    // transformation is described below, depending on the form of SCOPE's
    // conclusion.
    //
    // Note that after the original conclusion is rederived the new proof node
    // will actually have to be printed, respectively, (cl (=> (and F1 ... Fn)
    // F)) or (cl (not (and F1 ... Fn))).
    //
    // Let (not (and F1 ... Fn))^i denote the repetition of (not (and F1 ...
    // Fn)) for i times.
    //
    // T1:
    //
    //   P
    // ----- ANCHOR    ------- ... ------- AND_POS
    //  VP1             VP2_1  ...  VP2_n
    // ------------------------------------ RESOLUTION
    //               VP2a
    // ------------------------------------ REORDERING
    //  VP2b
    // ------ CONTRACTION           ------- IMPLIES_NEG1
    //   VP3                          VP4
    // ------------------------------------  RESOLUTION    ------- IMPLIES_NEG2
    //    VP5                                                VP6
    // ----------------------------------------------------------- RESOLUTION
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
    // Note that if n = 1, then the ANCHOR step yields (cl (not F1) F), which is
    // the same as VP3. Since VP1 = VP3, the steps for that transformation are
    // not generated.
    //
    //
    // If F = false:
    //
    //                                    --------- IMPLIES_SIMPLIFY
    //    T1                                 VP9
    // --------- CONTRACTION              --------- EQUIV_1
    //    VP8                                VP10
    // -------------------------------------------- RESOLUTION
    //          (cl (not (and F1 ... Fn)))*
    //
    // VP8: (cl (=> (and F1 ... Fn) false))
    // VP9: (cl (= (=> (and F1 ... Fn) false) (not (and F1 ... Fn))))
    // VP10: (cl (not (=> (and F1 ... Fn) false)) (not (and F1 ... Fn)))
    //
    //
    // Otherwise,
    //                T1
    //  ------------------------------ CONTRACTION
    //   (cl (=> (and F1 ... Fn) F))**
    //
    //
    // *  the corresponding proof node is (not (and F1 ... Fn))
    // ** the corresponding proof node is (=> (and F1 ... Fn) F)
    case PfRule::SCOPE:
    {
      bool success = true;

      // Build vp1
      std::vector<Node> negNode{d_cl};
      std::vector<Node> sanitized_args;
      for (Node arg : args)
      {
        negNode.push_back(arg.notNode());  // (not F1) ... (not Fn)
        sanitized_args.push_back(d_anc.convert(arg));
      }
      negNode.push_back(children[0]);  // (cl (not F1) ... (not Fn) F)
      Node vp1 = nm->mkNode(kind::SEXPR, negNode);
      success &= addAletheStep(AletheRule::ANCHOR_SUBPROOF,
                               vp1,
                               vp1,
                               children,
                               sanitized_args,
                               *cdp);

      Node andNode, vp3;
      if (args.size() == 1)
      {
        vp3 = vp1;
        andNode = args[0];  // F1
      }
      else
      {
        // Build vp2i
        andNode = nm->mkNode(kind::AND, args);  // (and F1 ... Fn)
        std::vector<Node> premisesVP2 = {vp1};
        std::vector<Node> notAnd = {d_cl, children[0]};  // cl F
        Node vp2_i;
        for (size_t i = 0, size = args.size(); i < size; i++)
        {
          vp2_i = nm->mkNode(kind::SEXPR, d_cl, andNode.notNode(), args[i]);
          success &=
              addAletheStep(AletheRule::AND_POS, vp2_i, vp2_i, {}, {}, *cdp);
          premisesVP2.push_back(vp2_i);
          notAnd.push_back(andNode.notNode());  // cl F (not (and F1 ... Fn))^i
        }

        Node vp2a = nm->mkNode(kind::SEXPR, notAnd);
        success &= addAletheStep(
            AletheRule::RESOLUTION, vp2a, vp2a, premisesVP2, options::proofAletheResPivots()?args:std::vector<Node>(), *cdp);

        notAnd.erase(notAnd.begin() + 1);  //(cl (not (and F1 ... Fn))^n)
        notAnd.push_back(children[0]);     //(cl (not (and F1 ... Fn))^n F)
        Node vp2b = nm->mkNode(kind::SEXPR, notAnd);
        success &=
            addAletheStep(AletheRule::REORDERING, vp2b, vp2b, {vp2a}, {}, *cdp);

        vp3 = nm->mkNode(kind::SEXPR, d_cl, andNode.notNode(), children[0]);
        success &=
            addAletheStep(AletheRule::CONTRACTION, vp3, vp3, {vp2b}, {}, *cdp);
      }

      Node vp8 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::IMPLIES, andNode, children[0]));

      Node vp4 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], andNode);
      success &=
          addAletheStep(AletheRule::IMPLIES_NEG1, vp4, vp4, {}, {}, *cdp);

      Node vp5 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0]);
      success &=
          addAletheStep(AletheRule::RESOLUTION, vp5, vp5, {vp4, vp3},options::proofAletheResPivots()?std::vector<Node>{andNode}:std::vector<Node>(),  *cdp);

      Node vp6 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], children[0].notNode());
      success &=
          addAletheStep(AletheRule::IMPLIES_NEG2, vp6, vp6, {}, {}, *cdp);

      Node vp7 = nm->mkNode(kind::SEXPR, d_cl, vp8[1], vp8[1]);
      success &=
          addAletheStep(AletheRule::RESOLUTION, vp7, vp7, {vp5, vp6}, options::proofAletheResPivots()?std::vector<Node>{children[0]}:std::vector<Node>(), *cdp);

      if (children[0] != nm->mkConst(false))
      {
        success &=
            addAletheStep(AletheRule::CONTRACTION, res, vp8, {vp7}, {}, *cdp);
      }
      else
      {
        success &=
            addAletheStep(AletheRule::CONTRACTION, vp8, vp8, {vp7}, {}, *cdp);

        Node vp9 =
            nm->mkNode(kind::SEXPR,
                       d_cl,
                       nm->mkNode(kind::EQUAL, vp8[1], andNode.notNode()));
        success &=
            addAletheStep(AletheRule::IMPLIES_SIMPLIFY, vp9, vp9, {}, {}, *cdp);

        Node vp10 =
            nm->mkNode(kind::SEXPR, d_cl, vp8[1].notNode(), andNode.notNode());
        success &=
            addAletheStep(AletheRule::EQUIV1, vp10, vp10, {vp9}, {}, *cdp);

        success &= addAletheStep(AletheRule::RESOLUTION,
                                 res,
                                 nm->mkNode(kind::SEXPR, d_cl, res),
                                 {vp8, vp10},
                                 options::proofAletheResPivots()?std::vector<Node>{vp8[1]}:std::vector<Node>(),
                                 *cdp);
      }

      return success;
    }
    case PfRule::DSL_REWRITE:
    {
      // get the name
      rewriter::DslPfRule di;
      Node rule;
      if (rewriter::getDslPfRule(args[0], di))
      {
        std::stringstream ss;
        ss << di;
        rule = nm->mkBoundVar(ss.str(), nm->sExprType());
      }
      else
      {
        Unreachable();
      }
      return addAletheStep(AletheRule::ALL_SIMPLIFY,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {rule},
                           *cdp);
    }
    case PfRule::EVALUATE:
    {
      return addAletheStep(AletheRule::ALL_SIMPLIFY,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {nm->mkBoundVar("evaluate", nm->sExprType())},
                           *cdp);
    }
    case PfRule::THEORY_REWRITE:
    {
      return addAletheStep(AletheRule::ALL_SIMPLIFY,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Resolution and N-ary Resolution
    // See proof_rule.h for documentation on the RESOLUTION and CHAIN_RESOLUTION
    // rule. This comment uses variable names as introduced there.
    //
    // Because the RESOLUTION rule is merely a special case of CHAIN_RESOLUTION,
    // the same translation can be used for both.
    //
    // The main complication for the translation of the rule is that in the case
    // that the conclusion C is (or G1 ... Gn), the result is ambigous. E.g.,
    //
    // (cl F1 (or F2 F3))    (cl (not F1))
    // -------------------------------------- RESOLUTION
    // (cl (or F2 F3))
    //
    // (cl F1 F2 F3)         (cl (not F1))
    // -------------------------------------- RESOLUTION
    // (cl F2 F3)
    //
    // both (cl (or F2 F3)) and (cl F2 F3) correspond to the same proof node (or
    // F2 F3). Thus, it has to be checked if C is a singleton clause or not.
    //
    // If C = (or F1 ... Fn) is a non-singleton clause, then:
    //
    //   VP1 ... VPn
    // ------------------ RESOLUTION
    //  (cl F1 ... Fn)*
    //
    // Else if, C = false:
    //
    //   VP1 ... VPn
    // ------------------ RESOLUTION
    //       (cl)*
    //
    // Otherwise:
    //
    //   VP1 ... VPn
    // ------------------ RESOLUTION
    //      (cl C)*
    //
    //  * the corresponding proof node is C
    case PfRule::RESOLUTION:
    case PfRule::CHAIN_RESOLUTION:
    {
      if (!expr::isSingletonClause(res, children, args))
      {
        return addAletheStepFromOr(
            AletheRule::RESOLUTION_OR, res, children, args, *cdp);
      }
      return addAletheStep(AletheRule::RESOLUTION_OR,
                           res,
                           res == nm->mkConst(false)
                               ? nm->mkNode(kind::SEXPR, d_cl)
                               : nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           args,
                           *cdp);
    }
    // ======== Factoring
    // See proof_rule.h for documentation on the FACTORING rule. This comment
    // uses variable names as introduced there.
    //
    // If C2 = (or F1 ... Fn) but C1 != (or C2 ... C2), then VC2 = (cl F1 ...
    // Fn) Otherwise, VC2 = (cl C2).
    //
    //    P
    // ------- CONTRACTION
    //   VC2*
    //
    // * the corresponding proof node is C2
    case PfRule::FACTORING:
    {
      if (res.getKind() == kind::OR)
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
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Reordering
    // This rule is translated according to the clauses pattern.
    case PfRule::REORDERING:
    {
      return addAletheStepFromOr(
          AletheRule::REORDERING, res, children, {}, *cdp);
    }
    // ======== Split
    // See proof_rule.h for documentation on the SPLIT rule. This comment
    // uses variable names as introduced there.
    //
    // --------- NOT_NOT      --------- NOT_NOT
    //    VP1                    VP2
    // -------------------------------- RESOLUTION
    //          (cl F (not F))*
    //
    // VP1: (cl (not (not (not F))) F)
    // VP2: (cl (not (not (not (not F)))) (not F))
    //
    // * the corresponding proof node is (or F (not F))
    case PfRule::SPLIT:
    {
      Node vp1 = nm->mkNode(
          kind::SEXPR, d_cl, args[0].notNode().notNode().notNode(), args[0]);
      Node vp2 = nm->mkNode(kind::SEXPR,
                              d_cl,
                              args[0].notNode().notNode().notNode().notNode(),
                              args[0].notNode());
      return addAletheStep(AletheRule::NOT_NOT, vp2, vp2, {}, {}, *cdp)
          && addAletheStep(AletheRule::NOT_NOT, vp1, vp1, {}, {}, *cdp)
          && addAletheStepFromOr(AletheRule::RESOLUTION, res, {vp1, vp2},
	     options::proofAletheResPivots()?std::vector<Node>{args[0].notNode().notNode().notNode()}:std::vector<Node>(), *cdp);
    }
    // ======== Equality resolution
    // See proof_rule.h for documentation on the EQ_RESOLVE rule. This
    // comment uses variable names as introduced there.
    //
    // If F1 = (or G1 ... Gn), then P1 will be printed as (cl G1 ... Gn) but
    // needs to be printed as (cl (or G1 ... Gn)). The only exception to this
    // are ASSUME steps that are always printed as (cl (or G1 ... Gn)) and
    // EQ_RESOLVE steps themselves.
    //
    //           ------  ...  ------ OR_NEG
    //   P1       VP21   ...   VP2n
    //  ---------------------------- RESOLUTION
    //              VP3
    //  ---------------------------- CONTRACTION
    //              VP4
    //
    //  for i=1 to n, VP2i: (cl (or G1 ... Gn) (not Gi))
    //  VP3: (cl (or G1 ... Gn)^n)
    //  VP4: (cl (or (G1 ... Gn))
    //
    //  Let child1 = VP4.
    //
    //
    // Otherwise, child1 = P1.
    //
    //
    // Then, if F2 = false:
    //
    //  ------ EQUIV_POS2
    //   VP1                P2    child1
    //  --------------------------------- RESOLUTION
    //                (cl)*
    //
    // Otherwise:
    //
    //  ------ EQUIV_POS2
    //   VP1                P2    child1
    //  --------------------------------- RESOLUTION
    //              (cl F2)*
    //
    // VP1: (cl (not (= F1 F2)) (not F1) F2)
    //
    // * the corresponding proof node is F2
    case PfRule::EQ_RESOLVE:
    {
      bool success = true;
      Node vp1 =
          nm->mkNode(kind::SEXPR,
                     {d_cl, children[1].notNode(), children[0].notNode(), res});
      Node child1 = children[0];

      // Transform (cl F1 ... Fn) into (cl (or F1 ... Fn))
      if (children[0].notNode() != children[1].notNode()
          && children[0].getKind() == kind::OR)
      {
        PfRule pr = cdp->getProofFor(child1)->getRule();
        if (pr != PfRule::ASSUME && pr != PfRule::EQ_RESOLVE)
        {
          std::vector<Node> clauses{d_cl};
          clauses.insert(clauses.end(),
                         children[0].begin(),
                         children[0].end());  //(cl G1 ... Gn)

          std::vector<Node> vp2Nodes{children[0]};
          std::vector<Node> resNodes{d_cl};
          for (size_t i = 0, size = children[0].getNumChildren(); i < size; i++)
          {
            Node vp2i = nm->mkNode(
                kind::SEXPR,
                d_cl,
                children[0],
                children[0][i].notNode());  //(cl (or G1 ... Gn) (not Gi))
            success &=
                addAletheStep(AletheRule::OR_NEG, vp2i, vp2i, {}, {}, *cdp);
            vp2Nodes.push_back(vp2i);
            resNodes.push_back(children[0]);
          }
          Node vp3 = nm->mkNode(kind::SEXPR, resNodes);
          success &= addAletheStep(
              AletheRule::RESOLUTION, vp3, vp3, vp2Nodes, options::proofAletheResPivots()?std::vector<Node>{children[0]}:std::vector<Node>(), *cdp);

          Node vp4 = nm->mkNode(kind::SEXPR, d_cl, children[0]);
          success &=
              addAletheStep(AletheRule::CONTRACTION, vp4, vp4, {vp3}, {}, *cdp);
          child1 = vp4;
        }
      }

      success &= addAletheStep(AletheRule::EQUIV_POS2, vp1, vp1, {}, {}, *cdp);

      return success &= addAletheStep(AletheRule::RESOLUTION,
                                      res,
                                      res == nm->mkConst(false)
                                          ? nm->mkNode(kind::SEXPR, d_cl)
                                          : nm->mkNode(kind::SEXPR, d_cl, res),
                                      {vp1, children[1], child1},
                                      options::proofAletheResPivots()?std::vector<Node>{children[1],children[0]}:std::vector<Node>(),
                                      *cdp);
    }
    // ======== Modus ponens
    // See proof_rule.h for documentation on the MODUS_PONENS rule. This comment
    // uses variable names as introduced there.
    //
    //     (P2:(=> F1 F2))
    // ------------------------ IMPLIES
    //  (VP1:(cl (not F1) F2))             (P1:F1)
    // -------------------------------------------- RESOLUTION
    //                   (cl F2)*
    //
    // * the corresponding proof node is F2
    case PfRule::MODUS_PONENS:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addAletheStep(
                 AletheRule::IMPLIES, vp1, vp1, {children[1]}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp1, children[0]},
			      options::proofAletheResPivots()?std::vector<Node>{children[0]}:std::vector<Node>(),
                              *cdp);
    }
    // ======== Double negation elimination
    // See proof_rule.h for documentation on the NOT_NOT_ELIM rule. This comment
    // uses variable names as introduced there.
    //
    // ---------------------------------- NOT_NOT
    //  (VP1:(cl (not (not (not F))) F))           (P:(not (not F)))
    // ------------------------------------------------------------- RESOLUTION
    //                            (cl F)*
    //
    // * the corresponding proof node is F
    case PfRule::NOT_NOT_ELIM:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addAletheStep(AletheRule::NOT_NOT, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp1, children[0]},
			      options::proofAletheResPivots()?std::vector<Node>{children[0]}:std::vector<Node>(),
                              *cdp);
    }
    // ======== Contradiction
    // See proof_rule.h for documentation on the CONTRA rule. This
    // comment uses variable names as introduced there.
    //
    //  P1   P2
    // --------- RESOLUTION
    //   (cl)*
    //
    // * the corresponding proof node is false
    case PfRule::CONTRA:
    {
      return addAletheStep(AletheRule::RESOLUTION,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl),
                           children,
                           options::proofAletheResPivots()?std::vector<Node>{children[0]}:std::vector<Node>(),
                           *cdp);
    }
    // ======== And elimination
    // This rule is translated according to the singleton pattern.
    case PfRule::AND_ELIM:
    {
      return addAletheStep(AletheRule::AND,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== And introduction
    // See proof_rule.h for documentation on the AND_INTRO rule. This
    // comment uses variable names as introduced there.
    //
    //
    // ----- AND_NEG
    //  VP1            P1 ... Pn
    // -------------------------- RESOLUTION
    //   (cl (and F1 ... Fn))*
    //
    // VP1:(cl (and F1 ... Fn) (not F1) ... (not Fn))
    //
    // * the corresponding proof node is (and F1 ... Fn)
    case PfRule::AND_INTRO:
    {
      std::vector<Node> neg_Nodes = {d_cl,res};
      for (size_t i = 0, size = children.size(); i < size; i++)
      {
        neg_Nodes.push_back(children[i].notNode());
      }
      Node vp1 = nm->mkNode(kind::SEXPR, neg_Nodes);

      std::vector<Node> new_children = {vp1};
      new_children.insert(new_children.end(), children.begin(), children.end());

      return addAletheStep(AletheRule::AND_NEG, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              new_children,
                           options::proofAletheResPivots()?children:std::vector<Node>(),
                              *cdp);
    }
    // ======== Not Or elimination
    // This rule is translated according to the singleton pattern.
    case PfRule::NOT_OR_ELIM:
    {
      return addAletheStep(AletheRule::NOT_OR,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Implication elimination
    // This rule is translated according to the clause pattern.
    case PfRule::IMPLIES_ELIM:
    {
      return addAletheStepFromOr(AletheRule::IMPLIES, res, children, {}, *cdp);
    }
    // ======== Not Implication elimination version 1
    // This rule is translated according to the singleton pattern.
    case PfRule::NOT_IMPLIES_ELIM1:
    {
      return addAletheStep(AletheRule::NOT_IMPLIES1,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Not Implication elimination version 2
    // This rule is translated according to the singleton pattern.
    case PfRule::NOT_IMPLIES_ELIM2:
    {
      return addAletheStep(AletheRule::NOT_IMPLIES2,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Various elimination rules
    // The following rules are all translated according to the clause pattern.
    case PfRule::EQUIV_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::EQUIV1, res, children, {}, *cdp);
    }
    case PfRule::EQUIV_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::EQUIV2, res, children, {}, *cdp);
    }
    case PfRule::NOT_EQUIV_ELIM1:
    {
      return addAletheStepFromOr(
          AletheRule::NOT_EQUIV1, res, children, {}, *cdp);
    }
    case PfRule::NOT_EQUIV_ELIM2:
    {
      return addAletheStepFromOr(
          AletheRule::NOT_EQUIV2, res, children, {}, *cdp);
    }
    case PfRule::XOR_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::XOR1, res, children, {}, *cdp);
    }
    case PfRule::XOR_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::XOR2, res, children, {}, *cdp);
    }
    case PfRule::NOT_XOR_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::NOT_XOR1, res, children, {}, *cdp);
    }
    case PfRule::NOT_XOR_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::NOT_XOR2, res, children, {}, *cdp);
    }
    case PfRule::ITE_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::ITE2, res, children, {}, *cdp);
    }
    case PfRule::ITE_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::ITE1, res, children, {}, *cdp);
    }
    case PfRule::NOT_ITE_ELIM1:
    {
      return addAletheStepFromOr(AletheRule::NOT_ITE2, res, children, {}, *cdp);
    }
    case PfRule::NOT_ITE_ELIM2:
    {
      return addAletheStepFromOr(AletheRule::NOT_ITE1, res, children, {}, *cdp);
    }
    //================================================= De Morgan rules
    // ======== Not And
    // This rule is translated according to the clause pattern.
    case PfRule::NOT_AND:
    {
      return addAletheStepFromOr(AletheRule::NOT_AND, res, children, {}, *cdp);
    }

    //================================================= CNF rules
    // The following rules are all translated according to the clause pattern.
    case PfRule::CNF_AND_POS:
    {
      return addAletheStepFromOr(AletheRule::AND_POS, res, children, {}, *cdp);
    }
    case PfRule::CNF_AND_NEG:
    {
      return addAletheStepFromOr(AletheRule::AND_NEG, res, children, {}, *cdp);
    }
    case PfRule::CNF_OR_POS:
    {
      return addAletheStepFromOr(AletheRule::OR_POS, res, children, {}, *cdp);
    }
    case PfRule::CNF_OR_NEG:
    {
      return addAletheStepFromOr(AletheRule::OR_NEG, res, children, {}, *cdp);
    }
    case PfRule::CNF_IMPLIES_POS:
    {
      return addAletheStepFromOr(
          AletheRule::IMPLIES_POS, res, children, {}, *cdp);
    }
    case PfRule::CNF_IMPLIES_NEG1:
    {
      return addAletheStepFromOr(
          AletheRule::IMPLIES_NEG1, res, children, {}, *cdp);
    }
    case PfRule::CNF_IMPLIES_NEG2:
    {
      return addAletheStepFromOr(
          AletheRule::IMPLIES_NEG2, res, children, {}, *cdp);
    }
    case PfRule::CNF_EQUIV_POS1:
    {
      return addAletheStepFromOr(
          AletheRule::EQUIV_POS2, res, children, {}, *cdp);
    }
    case PfRule::CNF_EQUIV_POS2:
    {
      return addAletheStepFromOr(
          AletheRule::EQUIV_POS1, res, children, {}, *cdp);
    }
    case PfRule::CNF_EQUIV_NEG1:
    {
      return addAletheStepFromOr(
          AletheRule::EQUIV_NEG2, res, children, {}, *cdp);
    }
    case PfRule::CNF_EQUIV_NEG2:
    {
      return addAletheStepFromOr(
          AletheRule::EQUIV_NEG1, res, children, {}, *cdp);
    }
    case PfRule::CNF_XOR_POS1:
    {
      return addAletheStepFromOr(AletheRule::XOR_POS1, res, children, {}, *cdp);
    }
    case PfRule::CNF_XOR_POS2:
    {
      return addAletheStepFromOr(AletheRule::XOR_POS2, res, children, {}, *cdp);
    }
    case PfRule::CNF_XOR_NEG1:
    {
      return addAletheStepFromOr(AletheRule::XOR_NEG2, res, children, {}, *cdp);
    }
    case PfRule::CNF_XOR_NEG2:
    {
      return addAletheStepFromOr(AletheRule::XOR_NEG1, res, children, {}, *cdp);
    }
    case PfRule::CNF_ITE_POS1:
    {
      return addAletheStepFromOr(AletheRule::ITE_POS2, res, children, {}, *cdp);
    }
    case PfRule::CNF_ITE_POS2:
    {
      return addAletheStepFromOr(AletheRule::ITE_POS1, res, children, {}, *cdp);
    }
    case PfRule::CNF_ITE_NEG1:
    {
      return addAletheStepFromOr(AletheRule::ITE_NEG2, res, children, {}, *cdp);
    }
    case PfRule::CNF_ITE_NEG2:
    {
      return addAletheStepFromOr(AletheRule::ITE_NEG1, res, children, {}, *cdp);
    }
    // ======== CNF ITE Pos version 3
    //
    // ----- ITE_POS1            ----- ITE_POS2
    //  VP1                       VP2
    // ------------------------------- RESOLUTION
    //             VP3
    // ------------------------------- REORDERING
    //             VP4
    // ------------------------------- CONTRACTION
    //  (cl (not (ite C F1 F2)) F1 F2)
    //
    // VP1: (cl (not (ite C F1 F2)) C F2)
    // VP2: (cl (not (ite C F1 F2)) (not C) F1)
    // VP3: (cl (not (ite C F1 F2)) F2 (not (ite C F1 F2)) F1)
    // VP4: (cl (not (ite C F1 F2)) (not (ite C F1 F2)) F1 F2)
    //
    // * the corresponding proof node is (or (not (ite C F1 F2)) F1 F2)
    case PfRule::CNF_ITE_POS3:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, {d_cl, res[0], args[0][0], res[2]});
      Node vp2 =
          nm->mkNode(kind::SEXPR, {d_cl, res[0], args[0][0].notNode(), res[1]});
      Node vp3 =
          nm->mkNode(kind::SEXPR, {d_cl, res[0], res[2], res[0], res[1]});
      Node vp4 =
          nm->mkNode(kind::SEXPR, {d_cl, res[0], res[0], res[1], res[2]});

      return addAletheStep(AletheRule::ITE_POS1, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::ITE_POS2, vp2, vp2, {}, {}, *cdp)
             && addAletheStep(
                 AletheRule::RESOLUTION, vp3, vp3, {vp1, vp2}, options::proofAletheResPivots()?std::vector<Node>{args[0][0]}:std::vector<Node>(), *cdp)
             && addAletheStep(AletheRule::REORDERING, vp4, vp4, {vp3}, {}, *cdp)
             && addAletheStepFromOr(
                 AletheRule::CONTRACTION, res, {vp4}, {}, *cdp);
    }
    // ======== CNF ITE Neg version 3
    //
    // ----- ITE_NEG1            ----- ITE_NEG2
    //  VP1                       VP2
    // ------------------------------- RESOLUTION
    //             VP3
    // ------------------------------- REORDERING
    //             VP4
    // ------------------------------- CONTRACTION
    //  (cl (ite C F1 F2) C (not F2))
    //
    // VP1: (cl (ite C F1 F2) C (not F2))
    // VP2: (cl (ite C F1 F2) (not C) (not F1))
    // VP3: (cl (ite C F1 F2) (not F2) (ite C F1 F2) (not F1))
    // VP4: (cl (ite C F1 F2) (ite C F1 F2) (not F1) (not F2))
    //
    // * the corresponding proof node is (or (ite C F1 F2) C (not F2))
    case PfRule::CNF_ITE_NEG3:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, {d_cl, res[0], args[0][0], res[2]});
      Node vp2 =
          nm->mkNode(kind::SEXPR, {d_cl, res[0], args[0][0].notNode(), res[1]});
      Node vp3 =
          nm->mkNode(kind::SEXPR, {d_cl, res[0], res[2], res[0], res[1]});
      Node vp4 =
          nm->mkNode(kind::SEXPR, {d_cl, res[0], res[0], res[1], res[2]});

      return addAletheStep(AletheRule::ITE_NEG1, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::ITE_NEG2, vp2, vp2, {}, {}, *cdp)
             && addAletheStep(
                 AletheRule::RESOLUTION, vp3, vp3, {vp1, vp2}, options::proofAletheResPivots()?std::vector<Node>{args[0][0]}:std::vector<Node>(), *cdp)
             && addAletheStep(AletheRule::REORDERING, vp4, vp4, {vp3}, {}, *cdp)
             && addAletheStepFromOr(
                 AletheRule::CONTRACTION, res, {vp4}, {}, *cdp);
    }
    //================================================= Equality rules
    // The following rules are all translated according to the singleton
    // pattern.
    case PfRule::REFL:
    {
      return addAletheStep(AletheRule::REFL,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    case PfRule::SYMM:
    {
      return addAletheStep(
          res.getKind() == kind::NOT ? AletheRule::NOT_SYMM : AletheRule::SYMM,
          res,
          nm->mkNode(kind::SEXPR, d_cl, res),
          children,
          {},
          *cdp);
    }
    case PfRule::TRANS:
    {
      return addAletheStep(AletheRule::TRANS,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           {},
                           *cdp);
    }
    // ======== Congruence
    // In the case that the kind of the function symbol f? is FORALL or
    // EXISTS, the cong rule needs to be converted into a bind rule. The first
    // n children will be refl rules, e.g. (= (v0 Int) (v0 Int)).
    //
    //  Let t1 = (BOUND_VARIABLE LIST (v1 A1) ... (vn An)) and s1 =
    //  (BOUND_VARIABLE LIST (v1 A1) ... (vn vn)).
    //
    //  ----- REFL ... ----- REFL
    //   VP1            VPn             P2
    //  --------------------------------------- bind,
    //                                          ((:= (v1 A1) v1) ...
    //                                          (:= (vn An) vn))
    //   (cl (= (forall ((v1 A1)...(vn An)) t2)
    //   (forall ((v1 B1)...(vn Bn)) s2)))**
    //
    //  VPi: (cl (= vi vi))*
    //
    //  * the corresponding proof node is (or (= vi vi))
    //
    // Otherwise, the rule follows the singleton pattern, i.e.:
    //
    //    P1 ... Pn
    //  -------------------------------------------------------- cong
    //   (cl (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn)))**
    //
    // ** the corresponding proof node is (= (<kind> f? t1 ... tn) (<kind> f?
    // s1 ... sn))
    case PfRule::CONG:
    {
      if (res[0].isClosure())
      {
        std::vector<Node> vpis;
        bool success = true;
        for (size_t i = 0, size = children[0][0].getNumChildren(); i < size;
             i++)
        {
          Node vpi = children[0][0][i].eqNode(children[0][1][i]);
          new_args.push_back(vpi);
          vpis.push_back(nm->mkNode(kind::SEXPR, d_cl, vpi));
          success &= addAletheStep(AletheRule::REFL, vpi, vpi, {}, {}, *cdp);
        }
        vpis.push_back(children[1]);
        return success
               && addAletheStep(AletheRule::ANCHOR_BIND,
                                res,
                                nm->mkNode(kind::SEXPR, d_cl, res),
                                vpis,
                                new_args,
                                *cdp);
      }
      return addAletheStep(AletheRule::CONG,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
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
    case PfRule::TRUE_INTRO:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, res.eqNode(children[0]));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, res, children[0].notNode());
      return addAletheStep(AletheRule::EQUIV_SIMPLIFY, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::EQUIV2, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp2, children[0]},
			      options::proofAletheResPivots()?std::vector<Node>{children[0]}:std::vector<Node>(),
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
    case PfRule::TRUE_ELIM:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].eqNode(res));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);
      return addAletheStep(AletheRule::EQUIV_SIMPLIFY, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::EQUIV1, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp2, children[0]},
			      options::proofAletheResPivots()?std::vector<Node>{children[0]}:std::vector<Node>(),
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
    case PfRule::FALSE_INTRO:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, res.eqNode(children[0]));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, res, children[0].notNode());
      Node vp3 = nm->mkNode(
          kind::SEXPR, d_cl, children[0].notNode().notNode(), children[0][0]);
      Node vp4 = nm->mkNode(kind::SEXPR, d_cl, res, children[0][0]);

      return addAletheStep(AletheRule::EQUIV_SIMPLIFY, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::EQUIV2, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::NOT_NOT, vp3, vp3, {}, {}, *cdp)
             && addAletheStep(
                 AletheRule::RESOLUTION, vp4, vp4, {vp2, vp3}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp4, children[0]},
			      options::proofAletheResPivots()?std::vector<Node>{children[0]}:std::vector<Node>(),
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
    case PfRule::FALSE_ELIM:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0].eqNode(res));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);

      return addAletheStep(AletheRule::EQUIV_SIMPLIFY, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::EQUIV1, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp2, children[0]},
			      options::proofAletheResPivots()?std::vector<Node>{children[0]}:std::vector<Node>(),
                              *cdp);
    }
    //================================================= Quantifiers rules
    // ======== Skolem intro
    /*case PfRule::SKOLEM_INTRO:
    {
      return
    addAletheStep(AletheRule::REFL,res,nm->mkNode(kind::SEXPR,d_cl,res),{},{},*cdp);
    }*/
    // ======== Skolemize
    // See proof_rule.h for documentation on the SKOLEMIZE rule. This
    // comment uses variable names as introduced there.
    //
    // If the conclusion is of the form F*sigma = not G:
    //
    //  ------------------------------------------------ SKO_EX
    //   (= (exists ((x1 T1) ... (xn Tn)) F) (F*sigma))
    //
    //  Then, apply the cvc5 rule EQ_RESOLVE to obtain F*sigma from this.
    //
    // Otherwise, if the child has the form (not (exist
    // case PfRule::SKOLEMIZE:
    // {
    // TODO: Add ANCHOR, map skolemized variable to substitutions skv_1
    // SkolemManager::getWitnessForm
    // Get choice term that corresponds to skv_1
    // F*sigma needs to be changed s.t. all occurences of skv_1 are replaced
    // with the choice term LOOK AT LEAN for replacement
    // NodeConverter will eventually be changed to do this
    // LeanNodeConverter
    // choice terms itself might contain skv variables
    // getSkolemTermVectors then I can get skolems
    //
    /*if (res.getKind() != kind::NOT)
    {
      Node choice;
      Node vp1 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::EQUAL, children[0], res));
      return addAletheStep(AletheRule::SKO_EX, vp1, vp1, {}, {}, *cdp)
             && cdp->addStep(
                 res, PfRule::EQ_RESOLVE, {vp1, children[0]}, args);
    }*/
    /*if (res.getKind() == kind::NOT)
    {
      std::cout << "children " << children << std::endl;
      std::cout << "res " << res << std::endl;
      std::cout << "skv_1 " << args << std::endl;
      Node temp = SkolemManager::getWitnessForm(res);
      std::cout << "children[0] " << children[0]
                << SkolemManager::getWitnessForm(children[0]) << std::endl;
      std::cout << "children[0][0][0][0] " << children[0][0][0][0] << "    "
                << SkolemManager::getWitnessForm(children[0][0][0][0])
                << std::endl;
      std::cout << "children[0][0][1] " << children[0][0][1]
                << SkolemManager::getWitnessForm(children[0][0][1])
                << std::endl;
      Node vp1 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::EQUAL, children[0][0], res));
      return addAletheStep(
                 AletheRule::ANCHOR_SKO_FORALL, vp1, vp1, {}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp1, children[0]},
                              {},
                              *cdp);
    }
    return addAletheStep(
        AletheRule::ALL_SIMPLIFY, res, res, {}, children, *cdp);
  }*/
    // ======== Instantiate
    // See proof_rule.h for documentation on the INSTANTIATE rule. This
    // comment uses variable names as introduced there.
    //
    // ----- FORALL_INST, (= x1 t1) ... (= xn tn)
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
    case PfRule::INSTANTIATE:
    {
      for (size_t i = 0, size = children[0][0].getNumChildren(); i < size; i++)
      {
        new_args.push_back(children[0][0][i].eqNode(args[i]));
      }
      Node vp1 = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::OR, children[0].notNode(), res));
      Node vp2 = nm->mkNode(kind::SEXPR, d_cl, children[0].notNode(), res);
      return addAletheStep(
                 AletheRule::FORALL_INST, vp1, vp1, {}, new_args, *cdp)
             && addAletheStep(AletheRule::OR, vp2, vp2, {vp1}, {}, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              {vp2, children[0]},
			      options::proofAletheResPivots()?std::vector<Node>{children[0]}:std::vector<Node>(),
                              *cdp);
    }
    // ======== Alpha Equivalence
    // See proof_rule.h for documentation on the ALPHA_EQUIV rule. This
    // comment uses variable names as introduced there.
    //
    // Let F = (forall ((y1 A1) ... (yn An)) G) and F*sigma = (forall ((z1 A1)
    // ... (zn An)) G*sigma)
    //
    //
    // -----    ----- REFL  ----- REFL
    //  VP1 .... VPn         VP
    // -------------------------- BIND, ((:= (y1 A1) z1) ... (:= (yn An) zn))
    //         (= F F*sigma)
    //
    // VPi: (cl (= yi zi))^
    // VP: (cl (= G G*sigma))
    //
    // ^ the corresponding proof node is F*sigma
    case PfRule::ALPHA_EQUIV:
    {
      // performance optimization
      // If y1 ... yn are mapped to y1 ... yn it suffices to use a refl step
      if (res[0].toString() == res[1].toString())
      {
        return addAletheStep(AletheRule::REFL,
                             res,
                             nm->mkNode(kind::SEXPR, d_cl, res),
                             {},
                             {},
                             *cdp);
      }

      std::vector<Node> new_children;
      bool success = true;
      for (size_t i = 1, size = args.size(); i < size; i++)
      {
        Node vpi = nm->mkNode(kind::SEXPR, d_cl, args[i]);
        new_children.push_back(vpi);
        success&& addAletheStep(AletheRule::REFL, vpi, vpi, {}, {}, *cdp);
      }
      Node vp = nm->mkNode(
          kind::SEXPR, d_cl, nm->mkNode(kind::EQUAL, res[0][1], res[1][1]));
      success&& addAletheStep(AletheRule::REFL, vp, vp, {}, {}, *cdp);
      new_children.push_back(vp);
      new_args.insert(new_args.begin(), args.begin() + 1, args.end());
      return success
             && addAletheStep(AletheRule::ANCHOR_BIND,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              new_children,
                              new_args,
                              *cdp);
    }
    //================================================= Arithmetic rules
    // ======== Adding Inequalities
    //
    // ----- LIA_GENERIC
    //  VP1                P1 ... Pn
    // ------------------------------- RESOLUTION
    //  (cl (>< t1 t2))*
    //
    // VP1: (cl (not l1) ... (not ln) (>< t1 t2))
    //
    // * the corresponding proof node is (>< t1 t2)
    case PfRule::MACRO_ARITH_SCALE_SUM_UB:
    {
      std::vector<Node> vp1s{d_cl};
      for (const Node& child : children)
      {
        vp1s.push_back(child.notNode());
      }
      vp1s.push_back(res);
      Node vp1 = nm->mkNode(kind::SEXPR, vp1s);
      std::vector<Node> new_children = {vp1};
      new_children.insert(new_children.end(), children.begin(), children.end());
      return addAletheStep(AletheRule::LIA_GENERIC, vp1, vp1, {}, args, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              new_children,
			      options::proofAletheResPivots()?children:std::vector<Node>(),
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
    case PfRule::INT_TIGHT_UB:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0], res);
      std::vector<Node> new_children = {vp1, children[0]};
      new_args.push_back(nm->mkConst<Rational>(CONST_RATIONAL, 1));
      return addAletheStep(AletheRule::LA_GENERIC, vp1, vp1, {}, new_args, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              new_children,
			      options::proofAletheResPivots()?children:std::vector<Node>(),
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
    case PfRule::INT_TIGHT_LB:
    {
      Node vp1 = nm->mkNode(kind::SEXPR, d_cl, children[0], res);
      std::vector<Node> new_children = {vp1, children[0]};
      new_args.push_back(nm->mkConst<Rational>(CONST_RATIONAL, 1));
      return addAletheStep(AletheRule::LA_GENERIC, vp1, vp1, {}, new_args, *cdp)
             && addAletheStep(AletheRule::RESOLUTION,
                              res,
                              nm->mkNode(kind::SEXPR, d_cl, res),
                              new_children,
			      options::proofAletheResPivots()?children:std::vector<Node>(),
                              *cdp);
    }
    // ======== Trichotomy of the reals
    // See proof_rule.h for documentation on the ARITH_TRICHOTOMY rule. This
    // comment uses variable names as introduced there.
    //
    // If C = (= x c) or C = (> x c) pre-processing has to transform (>= x c)
    // into (<= c x)
    //
    // ------------------------------------------------------ LA_DISEQUALITY
    //  (VP1: (cl (or (= x c) (not (<= x c)) (not (<= c x)))))
    // -------------------------------------------------------- OR
    //  (VP2: (cl (= x c) (not (<= x c)) (not (<= c x))))
    //
    // If C = (> x c) or C = (< x c) post-processing has to be added. In these
    // cases resolution on VP2 A B yields (not (<=x c)) or (not (<= c x)) and
    // comp_simplify is used to transform it into C. Otherwise,
    //
    //  VP2   A   B
    // ---------------- RESOLUTION
    //  (cl C)*
    //
    // * the corresponding proof node is C
    case PfRule::ARITH_TRICHOTOMY:
    {
      bool success = true;
      Node equal;
      Node lesser;
      Node greater;

      if (res.getKind() == kind::EQUAL)
      {
        equal = res;
        if (children[0].getKind() == kind::LEQ)
        {
          greater = children[0];
          lesser = children[1];
        }
        else
        {
          greater = children[1];
          lesser = children[0];
        }
      }
      // Add case where res is not =
      else if (res.getKind() == kind::GT)
      {
        greater = res;
        if (children[0].getKind() == kind::NOT)
        {
          equal = children[0];
          lesser = children[1];
        }
        else
        {
          equal = children[1];
          lesser = children[0];
        }
      }
      else
      {
        lesser = res;
        if (children[0].getKind() == kind::NOT)
        {
          equal = children[0];
          greater = children[1];
        }
        else
        {
          equal = children[1];
          greater = children[0];
        }
      }

      Node x;
      Node c;
      if (equal.getKind() == kind::NOT)
      {
        x = equal[0][0];
        c = equal[0][1];
      }
      else
      {
        x = equal[0];
        c = equal[1];
      }
      Node vp_child1 = children[0];
      Node vp_child2 = children[1];

      // Preprocessing
      if (res == equal || res == greater)
      {  // C = (= x c) or C = (> x c)
        // lesser = (>= x c)
        Node vpc2 = nm->mkNode(kind::SEXPR,
                               d_cl,
                               nm->mkNode(kind::EQUAL,
                                          nm->mkNode(kind::GEQ, x, c),
                                          nm->mkNode(kind::LEQ, c, x)));
        // (cl (= (>= x c) (<= c x)))
        Node vpc1 = nm->mkNode(kind::SEXPR,
                               {d_cl,
                                vpc2[1].notNode(),
                                nm->mkNode(kind::GEQ, x, c).notNode(),
                                nm->mkNode(kind::LEQ, c, x)});
        // (cl (not(= (>= x c) (<= c x))) (not (>= x c)) (<= c x))
        vp_child1 = nm->mkNode(
            kind::SEXPR, d_cl, nm->mkNode(kind::LEQ, c, x));  // (cl (<= c x))

        success &=
            addAletheStep(AletheRule::EQUIV_POS2, vpc1, vpc1, {}, {}, *cdp)
            && addAletheStep(
                AletheRule::COMP_SIMPLIFY, vpc2, vpc2, {}, {}, *cdp)
            && addAletheStep(AletheRule::RESOLUTION,
                             vp_child1,
                             vp_child1,
                             {vpc1, vpc2, lesser},
                             {},
                             *cdp);
        // greater = (<= x c) or greater = (not (= x c)) -> no preprocessing
        // necessary
        if (res == equal)
        {
          vp_child2 = greater;
        }
        else
        {
          vp_child2 = equal;
        }
      }

      // Process
      Node vp1 = nm->mkNode(kind::SEXPR,
                            d_cl,
                            nm->mkNode(kind::OR,
                                       nm->mkNode(kind::EQUAL, x, c),
                                       nm->mkNode(kind::LEQ, x, c).notNode(),
                                       nm->mkNode(kind::LEQ, c, x).notNode()));
      // (cl (or (= x c) (not (<= x c)) (not (<= c x))))
      Node vp2 = nm->mkNode(kind::SEXPR,
                            {d_cl,
                             nm->mkNode(kind::EQUAL, x, c),
                             nm->mkNode(kind::LEQ, x, c).notNode(),
                             nm->mkNode(kind::LEQ, c, x).notNode()});
      // (cl (= x c) (not (<= x c)) (not (<= c x)))
      success &=
          addAletheStep(AletheRule::LA_DISEQUALITY, vp1, vp1, {}, {}, *cdp)
          && addAletheStep(AletheRule::OR, vp2, vp2, {vp1}, {}, *cdp);

      // Postprocessing
      if (res == equal)
      {  // no postprocessing necessary
        return success
               && addAletheStep(AletheRule::RESOLUTION,
                                res,
                                nm->mkNode(kind::SEXPR, d_cl, res),
                                {vp2, vp_child1, vp_child2},
			        options::proofAletheResPivots()?std::vector<Node>{vp_child1,vp_child2}:std::vector<Node>(),
                                *cdp);
      }
      else if (res == greater)
      {  // have (not (<= x c)) but result should be (> x c)
        Node vp3 = nm->mkNode(
            kind::SEXPR,
            d_cl,
            nm->mkNode(kind::LEQ, x, c).notNode());  // (cl (not (<= x c)))
        Node vp4 = nm->mkNode(
            kind::SEXPR,
            {d_cl,
             nm->mkNode(kind::EQUAL,
                        nm->mkNode(kind::GT, x, c),
                        nm->mkNode(kind::LEQ, x, c).notNode())
                 .notNode(),
             nm->mkNode(kind::GT, x, c),
             nm->mkNode(kind::LEQ, x, c)
                 .notNode()
                 .notNode()});  // (cl (not(= (> x c) (not (<= x c)))) (> x c)
                                // (not (not (<= x c))))
        Node vp5 =
            nm->mkNode(kind::SEXPR,
                       d_cl,
                       nm->mkNode(kind::EQUAL,
                                  nm->mkNode(kind::GT, x, c),
                                  nm->mkNode(kind::LEQ, x, c).notNode()));
        // (cl (= (> x c) (not (<= x c))))

        return success
               && addAletheStep(AletheRule::RESOLUTION,
                                vp3,
                                vp3,
                                {vp2, vp_child1, vp_child2},
			        options::proofAletheResPivots()?std::vector<Node>{vp_child1,vp_child2}:std::vector<Node>(),
                                *cdp)
               && addAletheStep(AletheRule::EQUIV_POS1, vp4, vp4, {}, {}, *cdp)
               && addAletheStep(
                   AletheRule::COMP_SIMPLIFY, vp5, vp5, {}, {}, *cdp)
               && addAletheStep(AletheRule::RESOLUTION,
                                res,
                                nm->mkNode(kind::SEXPR, d_cl, res),
                                {vp3, vp4, vp5},
			        options::proofAletheResPivots()?std::vector<Node>{vp_child1,vp_child2}:std::vector<Node>(),
                                *cdp);
      }
      else
      {  // have (not (<= c x)) but result should be (< x c)
        Node vp3 = nm->mkNode(
            kind::SEXPR,
            d_cl,
            nm->mkNode(kind::LEQ, c, x).notNode());  // (cl (not (<= c x)))
        Node vp4 = nm->mkNode(
            kind::SEXPR,
            {d_cl,
             nm->mkNode(kind::EQUAL,
                        nm->mkNode(kind::LT, x, c),
                        nm->mkNode(kind::LEQ, c, x).notNode())
                 .notNode(),
             nm->mkNode(kind::LT, x, c),
             nm->mkNode(kind::LEQ, c, x)
                 .notNode()
                 .notNode()});  // (cl (not(= (< x c) (not (<= c x)))) (< x c)
                                // (not (not (<= c x))))
        Node vp5 = nm->mkNode(
            kind::SEXPR,
            d_cl,
            nm->mkNode(kind::EQUAL,
                       nm->mkNode(kind::LT, x, c),
                       nm->mkNode(kind::LEQ, c, x)
                           .notNode()));  // (cl (= (< x c) (not (<= c x))))

        return success
               && addAletheStep(AletheRule::RESOLUTION,
                                vp3,
                                vp3,
                                {vp2, vp_child1, vp_child2},
                                {},
                                *cdp)
               && addAletheStep(AletheRule::EQUIV_POS1, vp4, vp4, {}, {}, *cdp)
               && addAletheStep(
                   AletheRule::COMP_SIMPLIFY, vp5, vp5, {}, {}, *cdp)
               && addAletheStep(AletheRule::RESOLUTION,
                                res,
                                nm->mkNode(kind::SEXPR, d_cl, res),
                                {vp3, vp4, vp5},
			        options::proofAletheResPivots()?std::vector<Node>{vp_child1,vp_child2}:std::vector<Node>(),
                                *cdp);
      }
    }
    default:
    {
      Trace("alethe-proof")
          << "... rule not translated yet " << id << " / " << res << " "
          << children << " " << args << std::endl;
      std::cout << "UNTRANSLATED rule: " << id << std::endl;
      return addAletheStep(AletheRule::UNDEFINED,
                           res,
                           nm->mkNode(kind::SEXPR, d_cl, res),
                           children,
                           args,
                           *cdp);
    }
      Trace("alethe-proof")
          << "... error translating rule " << id << " / " << res << " "
          << children << " " << args << std::endl;
      return false;
  }

  Trace("alethe-proof") << "... error translating rule " << id << " / " << res
                        << " " << children << " " << args << std::endl;
  return false;
}

// Adds OR rule to the premises of a step if the premise is not a clause and
// should not be a singleton. Since FACTORING and REORDERING always take
// non-singletons, this adds an OR step to their premise if it was formerly
// printed as (cl (or F1 ... Fn)). For resolution, it is necessary to check all
// children to find out whether they're singleton before determining if they are
// already printed correctly.
bool AletheProofPostprocessCallback::finalize(Node res,
                                              PfRule id,
                                              const std::vector<Node>& children,
                                              const std::vector<Node>& args,
                                              CDProof* cdp)
{
  NodeManager* nm = NodeManager::currentNM();
  AletheRule rule = getAletheRule(args[0]);
  Trace("alethe-proof") << "... finalizer for rule " << rule << " / " << res
                        << std::endl;
  switch (rule)
  {
    // In the case of a resolution rule the rule might originally have been a
    // cvc5 RESOLUTION or CHAIN_RESOLUTION rule. In these cases it is possible
    // that one of the children was printed as (cl (or F1 ... Fn)) but used as
    // (cl F1 ... Fn). However, since the information about the pivot of the
    // resolution step the child is used in is provided it is always possible
    // to figure out if an additional OR step is necessary.
    case AletheRule::RESOLUTION_OR:
    {
      if (args.size() < 4)
      {
        return false;
      }
      std::vector<Node> new_children = children;
      std::vector<Node> new_args =
          options::proofAletheResPivots()
              ? args
              : std::vector<Node>(args.begin(), args.begin() + 3);
      Node trueNode = nm->mkConst(true);
      Node falseNode = nm->mkConst(false);
      bool hasUpdated = false;

      // The first child is used as a non-singleton clause if it is not equal
      // to its pivot L_1. Since it's the first clause in the resolution it can
      // only be equal to the pivot in the case the polarity is true.
      if (children[0].getKind() == kind::OR
          && (args[3] != trueNode || children[0] != args[4]))
      {
        std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[0]);
        Node childConclusion = childPf->getArguments()[2];
        AletheRule childRule = getAletheRule(childPf->getArguments()[0]);
        // if child conclusion is of the form (sexpr cl (or ...)), then we need
        // to add an OR step, since this child must not be a singleton
        if ((childConclusion.getNumChildren() == 2 && childConclusion[0] == d_cl
             && childConclusion[1].getKind() == kind::OR)
            || (childRule == AletheRule::ASSUME
                && childConclusion.getKind() == kind::OR))
        {
          hasUpdated = true;
          // Add or step
          std::vector<Node> subterms{d_cl};
          if (childRule == AletheRule::ASSUME)
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
          Node newConclusion = nm->mkNode(kind::SEXPR, subterms);
          addAletheStep(AletheRule::OR,
                        newConclusion,
                        newConclusion,
                        {children[0]},
                        {},
                        *cdp);
          new_children[0] = newConclusion;
          Trace("alethe-proof")
              << "Added OR step in finalizer " << childConclusion << " / "
              << newConclusion << std::endl;
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
        if (children[i].getKind() == kind::OR
            && (args[2 * (i - 1) + 3] != falseNode
                || args[2 * (i - 1) + 1 + 3] != children[i]))
        {
          std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[i]);
          Node childConclusion = childPf->getArguments()[2];
          AletheRule childRule = getAletheRule(childPf->getArguments()[0]);
          // Add or step
          if ((childConclusion.getNumChildren() == 2
               && childConclusion[0] == d_cl
               && childConclusion[1].getKind() == kind::OR)
              || childRule == AletheRule::ASSUME
                     && childConclusion.getKind() == kind::OR)
          {
            hasUpdated = true;
            std::vector<Node> lits{d_cl};
            if (childRule == AletheRule::ASSUME)
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
            Node conclusion = nm->mkNode(kind::SEXPR, lits);
            addAletheStep(AletheRule::OR,
                          conclusion,
                          conclusion,
                          {children[i]},
                          {},
                          *cdp);
            new_children[i] = conclusion;
            Trace("alethe-proof")
                << "Added OR step in finalizer" << childConclusion << " / "
                << conclusion << std::endl;
          }
        }
      }
      if (hasUpdated || !options::proofAletheResPivots())
      {
        Trace("alethe-proof")
            << "... update alethe step in finalizer " << res << " "
            << new_children << " / " << args << std::endl;
        cdp->addStep(res, PfRule::ALETHE_RULE, new_children, new_args);
        return true;
      }
      return false;
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
    // The process is anagolous for REORDERING.
    case AletheRule::REORDERING:
    case AletheRule::CONTRACTION:
    {
      std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[0]);
      Node childConclusion = childPf->getArguments()[2];
      AletheRule childRule = getAletheRule(childPf->getArguments()[0]);
      if ((childConclusion.getNumChildren() == 2 && childConclusion[0] == d_cl
           && childConclusion[1].getKind() == kind::OR)
          || (childRule == AletheRule::ASSUME
              && childConclusion.getKind() == kind::OR))
      {
        // Add or step for child
        std::vector<Node> subterms{d_cl};
        if (getAletheRule(childPf->getArguments()[0]) == AletheRule::ASSUME)
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
        Node newChild = nm->mkNode(kind::SEXPR, subterms);
        addAletheStep(
            AletheRule::OR, newChild, newChild, {children[0]}, {}, *cdp);
        Trace("alethe-proof")
            << "Added OR step in finalizer to child " << childConclusion
            << " / " << newChild << std::endl;
        // update res step
        cdp->addStep(res, PfRule::ALETHE_RULE, {newChild}, args);
        return true;
      }
      return false;
    }
    default: return false;
  }
  return false;
}

// The last step of the proof was:
//
// Children:  (P1:C1) ... (Pn:Cn)
// Arguments: (AletheRule::VRULE,false,(cl false))
// ---------------------
// Conclusion: (false)
//
// In Alethe:
//
//  P1 ... Pn
// ------------------- VRULE   ---------------------- FALSE
//  (VP1:(cl false))*           (VP2:(cl (not true)))
// -------------------------------------------------- RESOLUTION
//                       (cl)**
//
// *  the corresponding proof node is ((false))
// ** the corresponding proof node is (false)
bool AletheProofPostprocessCallback::finalStep(
    Node res,
    PfRule id,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp)
{
  NodeManager* nm = NodeManager::currentNM();
  Node falseNode = nm->mkConst(false);

  if (
      // If the last proof rule was not translated yet
      (id == PfRule::ALETHE_RULE) &&
      // This case can only occur if the last step is an assumption
      (args[2].getNumChildren() > 1) &&
      // If the proof node has result (false) additional steps have to be added.
      (args[2][1] != falseNode))
  {
    return false;
  }

  // remove attribute for outermost scope
  if (id != PfRule::ALETHE_RULE)
  {
    std::vector<Node> sanitized_args{
        res,
        res,
        nm->mkConst<Rational>(CONST_RATIONAL,
                              static_cast<unsigned>(AletheRule::ASSUME))};
    for (const Node& arg : args)
    {
      sanitized_args.push_back(d_anc.convert(arg));
    }
    return cdp->addStep(res, PfRule::ALETHE_RULE, children, sanitized_args);
  }

  bool success = true;
  Node vp1 = nm->mkNode(kind::SEXPR, res);    // ((false))
  Node vp2 = nm->mkConst(false).notNode();    // (not true)
  Node res2 = nm->mkNode(kind::SEXPR, d_cl);  // (cl)
  AletheRule vrule = getAletheRule(args[0]);

  // In the special case that false is an assumption, we print false instead of
  // (cl false)
  success &= addAletheStep(
      vrule,
      vp1,
      (vrule == AletheRule::ASSUME ? res : nm->mkNode(kind::SEXPR, d_cl, res)),
      children,
      {},
      *cdp);
  Trace("alethe-proof") << "... add Alethe step " << vp1 << " / "
                        << nm->mkNode(kind::SEXPR, d_cl, res) << " " << vrule
                        << " " << children << " / {}" << std::endl;

  success &= addAletheStep(
      AletheRule::FALSE, vp2, nm->mkNode(kind::SEXPR, d_cl, vp2), {}, {}, *cdp);
  Trace("alethe-proof") << "... add Alethe step " << vp2 << " / "
                        << nm->mkNode(kind::SEXPR, d_cl, vp2) << " "
                        << AletheRule::FALSE << " {} / {}" << std::endl;

  success &=
      addAletheStep(AletheRule::RESOLUTION, res, res2, {vp2, vp1},
			        options::proofAletheResPivots()?std::vector<Node>{res}:std::vector<Node>(), *cdp);
  Trace("alethe-proof") << "... add Alethe step " << res << " / " << res2 << " "
                        << AletheRule::RESOLUTION << " {" << vp2 << ", " << vp1
                        << " / {}" << std::endl;
  if (!success)
  {
    Trace("alethe-proof") << "... Error while printing final steps"
                          << std::endl;
  }

  return true;
}

bool AletheProofPostprocessCallback::addAletheStep(
    AletheRule rule,
    Node res,
    Node conclusion,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  // delete attributes
  Node sanitized_conclusion = conclusion;
  if (expr::hasClosure(conclusion))
  {
    sanitized_conclusion = d_anc.convert(conclusion);
  }

  std::vector<Node> new_args = std::vector<Node>();
  new_args.push_back(NodeManager::currentNM()->mkConst(
      CONST_RATIONAL, Rational(static_cast<unsigned>(rule))));
  new_args.push_back(res);
  new_args.push_back(sanitized_conclusion);
  new_args.insert(new_args.end(), args.begin(), args.end());
  Trace("alethe-proof") << "... add alethe step " << res << " / " << conclusion
                        << " " << rule << " " << children << " / " << new_args
                        << std::endl;
  return cdp.addStep(res, PfRule::ALETHE_RULE, children, new_args);
}

bool AletheProofPostprocessCallback::addAletheStepFromOr(
    AletheRule rule,
    Node res,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> subterms = {d_cl};
  subterms.insert(subterms.end(), res.begin(), res.end());
  Node conclusion = NodeManager::currentNM()->mkNode(kind::SEXPR, subterms);
  return addAletheStep(rule, res, conclusion, children, args, cdp);
}

AletheProofPostprocessNoSubtypeCallback::
    AletheProofPostprocessNoSubtypeCallback(ProofNodeManager* pnm)
    : d_pnm(pnm)
{
  d_finalizeRules = {
      AletheRule::CONG, AletheRule::TRANS, AletheRule::FORALL_INST};
  NodeManager* nm = NodeManager::currentNM();
  d_cl = nm->mkBoundVar("cl", nm->sExprType());
}

bool AletheProofPostprocessNoSubtypeCallback::shouldUpdate(
    std::shared_ptr<ProofNode> pn,
    const std::vector<Node>& fa,
    bool& continueUpdate)
{
  return true;
}

bool AletheProofPostprocessNoSubtypeCallback::update(
    Node res,
    PfRule id,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp,
    bool& continueUpdate)
{
  AletheRule rule = getAletheRule(args[0]);

  Trace("alethe-proof-subtyping")
      << "AletheProofPostprocessNoSubtypeCallback::update: " << res << " "
      << rule << " " << children << " / " << args << std::endl;
  // AlwaysAssert(args.size() >= 3);
  // traverse conclusion and any other args and update them
  bool changed = false;
  std::vector<Node> newArgs{args[0], args[1]};
  for (size_t i = 2, size = args.size(); i < size; ++i)
  {
    newArgs.push_back(d_anc.convert(args[i]));
    changed |= newArgs.back() != args[i];
  }
  if (changed)
  {
    Trace("alethe-proof-subtyping")
        << "\tConvertion changed " << args << " into " << newArgs << "\n";
    // whether new conclusion became (= A A) or (cl (= A A))
    if ((newArgs[2].getKind() == kind::EQUAL && newArgs[2][0] == newArgs[2][1])
        || (newArgs[2].getKind() == kind::SEXPR
            && newArgs[2].getNumChildren() == 2
            && newArgs[2][1].getKind() == kind::EQUAL
            && newArgs[2][1][0] == newArgs[2][1][1]))
    {
      Trace("alethe-proof-subtyping") << "\tTrivialized into REFL\n";
      // turn this step into a REFL one, ignore children and remaining arguments
      newArgs[0] = NodeManager::currentNM()->mkConst<Rational>(
          CONST_RATIONAL, static_cast<unsigned>(AletheRule::REFL));
      cdp->addStep(res, id, {}, {newArgs.begin(), newArgs.begin() + 3});
    }
    else
    {
      cdp->addStep(res, id, children, newArgs);
    }
    return true;
  }
  return false;
}

bool AletheProofPostprocessNoSubtypeCallback::finalize(
    Node res,
    PfRule id,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp)
{
  AletheRule rule = getAletheRule(args[0]);
  if (d_finalizeRules.find(rule) == d_finalizeRules.end())
  {
    return false;
  }
  Trace("alethe-proof-subtyping")
      << "AletheProofPostprocessNoSubtypeCallback::finalize: " << res << " "
      << rule << " " << children << " / " << args << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  bool updated = false;
  std::vector<Node> newChildren = children;
  switch (rule)
  {
    case AletheRule::TRANS:
    {
      // get children
      size_t size = children.size();
      const std::vector<Node>& child0Args =cdp->getProofFor(children[0])->getArguments();
      AlwaysAssert(child0Args.size() >= 3);
      AlwaysAssert(child0Args[2].getKind() != kind::SEXPR
                   || child0Args[2].getNumChildren() == 2);
      Node lastLink = child0Args[2].getKind() == kind::SEXPR ? child0Args[2][1]
                                                             : child0Args[2];
      // for each child check that the link in the transitivity chain is
      // compatible with the previous one. Otherwise add a step that casts
      // correctly
      for (size_t i = 1; i < size; ++i)
      {
        const std::vector<Node>& childArgs =
            cdp->getProofFor(children[i])->getArguments();
        AlwaysAssert(childArgs.size() >= 3);
        AlwaysAssert(childArgs[2].getKind() != kind::SEXPR
                     || childArgs[2].getNumChildren() == 2);
        Node childConclusion = childArgs[2].getKind() == kind::SEXPR
                                   ? childArgs[2][1]
                                   : childArgs[2];
        Node links[2] = {lastLink, childConclusion};
        AlwaysAssert(links[0].getKind() == kind::EQUAL
                     && links[1].getKind() == kind::EQUAL)
            << "not equalities: " << links[0] << " .. " << links[1] << "\n";
        if (links[0][1] == links[1][0])
        {
          lastLink = links[1];
          continue;
        }
        updated = true;
        Trace("alethe-proof-subtyping")
            << "\t..links l_" << (i - 1) << "[1] and l_" << i
            << "[0] differ:\n\t\t\t" << links[0][1] << " .. " << links[1][0]
            << "\n";
        // AlwaysAssert(links[0][1].getType().isReal()
        //              && links[1][0].getType().isReal());
        // Necessarily one of the differing terms has an integer subterm that is
        // a real subterm in the respective position of the other term. Both
        // should be lifted to reals via a new step which will proxy the
        // previous link into the chain
        // AlwaysAssert(!links[0][1].getType().isInteger()
        //              || links[1][0].getType().isInteger());
        // We test which is the "int link" by the heuristic that the it's the
        // one without CAST_TO_REAL / TO_REAL
        size_t intLink = !expr::hasSubtermKinds(
                             {kind::CAST_TO_REAL, kind::TO_REAL}, links[0][1])
                             ? 0
                             : 1;
        // size_t intLink = links[0][1].getType().isInteger() ? 0 : 1;
        size_t childUpdatedIndex = i - (1 - intLink);
        Trace("alethe-proof-subtyping")
            << "\t..int link is l_" << childUpdatedIndex << ": "
            << links[intLink] << "\n";
        // if (Configuration::isAssertionBuild())
        // {
        // for (size_t j = 0; j < 2; ++j)
        // {
        //   AlwaysAssert(links[intLink][1 - j].isConst()
        //                || !expr::hasSubtermKinds({kind::APPLY_UF,
        //                kind::SKOLEM},
        //                                          links[intLink][1 - j]))
        //       << "Unconvertable " << links[intLink][1 - j];
        // }
        // }
        AlwaysAssert(
            d_anc.traverseAndConvertAllConsts(links[intLink][1 - intLink])
            == links[1 - intLink][intLink]);
        // Add step for proxy
        Node newChild =
            nm->mkNode(kind::SEXPR,
                       // d_cl
                       d_cl,
                       // converted link
                       d_anc.traverseAndConvertAllConsts(links[intLink]));
        Trace("alethe-proof-subtyping")
            << "\t..new l_" << childUpdatedIndex << ": " << newChild << "\n";
        cdp->addStep(newChild,
                     PfRule::ALETHE_RULE,
                     {children[childUpdatedIndex]},
                     {nm->mkConst<Rational>(
                          CONST_RATIONAL,
                          static_cast<unsigned>(AletheRule::ALL_SIMPLIFY)),
                      newChild,
                      newChild});
        // update children
        newChildren[childUpdatedIndex] = newChild;
        // get new running last link
        lastLink = newChild[1];
      }
      // Update proof step with new premises
      if (updated)
      {
        // it must be the case that conclusion reflects new premises, i.e. that
        // conclusion t1 = tn means that first premise has (as printed
        // conclusion) "t1 = ..." and and last premise has "... = tn".
        AlwaysAssert(
            args[2][1][0]
                == cdp->getProofFor(newChildren[0])->getArguments()[2][1][0]
            && args[2][1][1]
                   == cdp->getProofFor(newChildren.back())
                          ->getArguments()[2][1][1]);
        cdp->addStep(res, PfRule::ALETHE_RULE, newChildren, args);
        return true;
      }
      break;
    }
    case AletheRule::CONG:
    {
      // given conclusion (= (f t11' ... tn1') (f t12' ... tn2')), for each
      // child (= ti1 ti2), check whether ti{1,2} is the same as ti{1,2}'. If
      // not, then we need to add a proxy step to the premise if ti{1,2}
      // is integer and, if ti{1,2}' is integer, change the conclusion.
      //
      // An invariant is probably that I don't need to check ti1' vs ti2'
      // because the above checks should cover this.
      Node conclusion = args[2][1];
      std::vector<Node> newConclusionChildren[2];
      newConclusionChildren[0] = {conclusion[0].begin(), conclusion[0].end()};
      newConclusionChildren[1] = {conclusion[1].begin(), conclusion[1].end()};
      for (size_t i = 0, size = children.size(); i < size; ++i)
      {
        const std::vector<Node>& childArgs = cdp->getProofFor(children[i])->getArguments();
        AlwaysAssert(childArgs.size() >= 3);
        AlwaysAssert(childArgs[2].getKind() != kind::SEXPR
                     || childArgs[2].getNumChildren() == 2);
        Node childConclusion = childArgs[2].getKind() == kind::SEXPR
                                   ? childArgs[2][1]
                                   : childArgs[2];
        Trace("alethe-proof-subtyping")
            << "\t..original conclusion " << i << ": " << childConclusion << "\n";

        size_t differ[2] = {conclusion[0][i] != childConclusion[0] ? i : size,
                            conclusion[1][i] != childConclusion[1] ? i : size};
        if (differ[0] < size || differ[1] < size)
        {
          updated = true;
          Trace("alethe-proof-subtyping")
              << "\t..child " << i << ": " << childConclusion << "\n";
          Trace("alethe-proof-subtyping")
              << "\t.." << i << "-th child/conclusion args differ on positions "
              << (differ[0] < size ? "0 " : "") << (differ[1] < size ? "1" : "")
              << " of conclusion equality\n";
          // Determine wether to add proxy step. Note that this is not something
          // trivial, as it effectively amounts to a rewriting proof, since the
          // part of the term to change may be deep within the term. Consider
          // the example
          //
          //          ... (= ti1 ti2) ...
          // -------------------------------------- CONG
          // (= (f ... ti1' ...) (f ... ti2' ...))
          //
          // where ti2 != ti2' but they're not integer or real terms. Rather
          // they're arbitrary terms that contain subterms t and t' which are
          // one integer and one real (and not integer). To determine who of
          // t/t' is the "true" real, we apply the heuristic of, according to
          // which of ti{1,2}/ti{1,2}' differ, whether ti{1,2} contains casts.
          // If it does not, then we assume that its differing subterm t is an
          // integer.
          //
          // TODO: the foolproof way is to traverse both simultaneously until we
          // find the difference (i.e. t vs t'), check how they differ, and
          // determine whether the premise is the "integer one".
          bool updateChild = !expr::hasSubtermKinds(
              {kind::CAST_TO_REAL, kind::TO_REAL},
              differ[0] == size ? childConclusion[1] : childConclusion[0]);
          // bool updateChild = childConclusion[0].getType().isInteger();
          if (updateChild)
          {
            Trace("alethe-proof-subtyping")
                << "\t..need proxy step for child\n";
            Node newChild =
                nm->mkNode(kind::SEXPR,
                           // d_cl
                           d_cl,
                           // converted link
                           d_anc.traverseAndConvertAllConsts(childConclusion));
            Trace("alethe-proof-subtyping")
                << "\t\t..new child " << newChild << "\n";
            cdp->addStep(newChild,
                         PfRule::ALETHE_RULE,
                         {children[i]},
                         {nm->mkConst<Rational>(
                              CONST_RATIONAL,
                              static_cast<unsigned>(AletheRule::ALL_SIMPLIFY)),
                          newChild,
                          newChild});
            // update children
            newChildren[i] = newChild;
          }
          // Whether to change conclusion
          for (size_t j = 0; j < 2; ++j)
          {
            Node childArgToCompare =
                updateChild ? newChildren[i][1][j] : childConclusion[j];
            // We need to change conclusion if conclusion[j][i] is different
            // from childArgToCompare, in which case necessarily
            // conclusion[j][i] has a differing integer subterm from a real one
            // in childArgToCompare
            if (conclusion[j][i] != childArgToCompare)
            // if (conclusion[j][i].getType().isInteger()
            //     && (differ[j] < size || updateChild))
            {
              Trace("alethe-proof-subtyping")
                  << "\t..need update " << i << "-th arg of conclusion[" << j
                  << "]\n";
              newConclusionChildren[j][i] = childArgToCompare;
              // newConclusionChildren[j][i] =
              //     d_anc.traverseAndConvertAllConsts(conclusion[j][i]);
              AlwaysAssert(d_anc.traverseAndConvertAllConsts(conclusion[j][i])
                           == childArgToCompare)
                  << "Converted " << conclusion[j][i] << " differ from "
                  << childArgToCompare << "\n";
              Trace("alethe-proof-subtyping")
                  << "\t\t..arg " << conclusion[j][i] << " became "
                  << childArgToCompare << "\n";
            }
          }
        }
      }
      // Update proof step with new premises and possibly new conclusion
      if (updated)
      {
        std::vector<Node> newArgs = args;
        Kind k = conclusion[0].getKind();
        if (kind::metaKindOf(k) == kind::metakind::PARAMETERIZED)
        {
          Node op = conclusion[0].getOperator();
          newConclusionChildren[0].insert(newConclusionChildren[0].begin(), op);
          newConclusionChildren[1].insert(newConclusionChildren[1].begin(), op);
        }
        Node maybeNewConclusion =
            nm->mkNode(k, newConclusionChildren[0])
                .eqNode(nm->mkNode(k, newConclusionChildren[1]));
        if (conclusion != maybeNewConclusion)
        {
          Trace("alethe-proof-subtyping")
              << "\t..updated conclusion to " << maybeNewConclusion << "\n";
          newArgs[2] = nm->mkNode(kind::SEXPR, args[2][0], maybeNewConclusion);
        }
        cdp->addStep(res, PfRule::ALETHE_RULE, newChildren, newArgs);
        return true;
      }
      break;
    }
    case AletheRule::FORALL_INST:
    {
      // do substitution on quantifier body. If different, then just replace
      //
      // Conclusion (args[2]) is of the form:
      //   (sexpr cl (or (not (forall (...) body)) inst))
      Node body = args[2][1][0][0][1];
      Node inst = args[2][1][1];
      // subs are stored in args[3..] as (= v t)
      std::vector<Node> vars, subs;
      for (size_t i = 3, nc = args.size(); i < nc; ++i)
      {
        AlwaysAssert(args[i].getKind() == kind::EQUAL) << args[i];
        vars.push_back(args[i][0]);
        subs.push_back(args[i][1]);
      }
      Node bodyInst =
          body.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      // when this happen it's always the instance who is in the wrong: a real
      // variable may be instantiated with an integer, but the opposite is not
      // possible
      if (bodyInst != inst)
      {
        Trace("alethe-proof-subtyping")
            << "\t..quantif body instantiated " << bodyInst
            << "\n\t..differs from the original " << inst << "\n";
        std::vector<Node> newArgs = args;
        // Rebuild conclusion. The negated forall is the same, only the inst
        // changes.
        Node newConclusion = nm->mkNode(kind::OR, args[2][1][0], bodyInst);
        Trace("alethe-proof-subtyping")
            << "\t..updated original conclusion " << args[2][1] << " to "
            << newConclusion << "\n";
        newArgs[2] = nm->mkNode(kind::SEXPR, args[2][0], newConclusion);
        newArgs[1] = newArgs[2];
        cdp->addStep(newArgs[2], PfRule::ALETHE_RULE, children, newArgs);
        Trace("alethe-proof-subtyping")
            << "\t..add a trust step to derive original conclusion from fixed "
               "one\n";
        // Add a new step that derives the original conclusion from the lifting
        // of the modified body. This way we don't need to change the rest of
        // the proof on account of the wrong instantiation
        cdp->addStep(res,
                     PfRule::ALETHE_RULE,
                     {newArgs[2]},
                     {nm->mkConst<Rational>(
                          CONST_RATIONAL,
                          static_cast<unsigned>(AletheRule::ALL_SIMPLIFY)),
                      res,
                      args[2]});
        return true;
      }
      break;
    }
    default:
    {
      break;
    }
  }
  AlwaysAssert(args.size() >= 3);
  return false;
}

AletheProofPostprocess::AletheProofPostprocess(ProofNodeManager* pnm,
                                               AletheNodeConverter& anc)
    : d_pnm(pnm), d_cb(d_pnm, anc), d_nst(d_pnm)
{
}

AletheProofPostprocess::~AletheProofPostprocess() {}

void AletheProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  // Translate proof node
  ProofNodeUpdater updater(d_pnm, d_cb, false, false, true);
  updater.process(pf->getChildren()[0]);

  // In the Alethe proof format the final step has to be (cl). However, after
  // the translation it might be (cl false). In that case additional steps are
  // required.
  // The function has the additional purpose of sanitizing the attributes of the
  // first SCOPE
  CDProof cpf(d_pnm, nullptr, "ProofNodeUpdater::CDProof", true);
  const std::vector<std::shared_ptr<ProofNode>>& cc = pf->getChildren();
  std::vector<Node> ccn;
  for (const std::shared_ptr<ProofNode>& cp : cc)
  {
    Node cpres = cp->getResult();
    ccn.push_back(cpres);
    // store in the proof
    cpf.addProof(cp);
  }
  if (d_cb.finalStep(
          pf->getResult(), pf->getRule(), ccn, pf->getArguments(), &cpf))
  {
    std::shared_ptr<ProofNode> npn = cpf.getProofFor(pf->getResult());

    // then, update the original proof node based on this one
    Trace("pf-process-debug") << "Update node..." << std::endl;
    d_pnm->updateNode(pf.get(), npn.get());
    Trace("pf-process-debug") << "...update node finished." << std::endl;
  }

  Trace("alethe-proof-subtyping") << "\n--------------------------------\n";
  ProofNodeUpdater finalFinal(d_pnm, d_nst, false, false, true);
  finalFinal.process(pf->getChildren()[0]);
}

}  // namespace proof

}  // namespace cvc5
