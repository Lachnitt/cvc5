/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for printing Alethe proof nodes.
 */

#include "proof/alethe/alethe_printer.h"

#include <iostream>
#include <unordered_map>

#include "proof/alethe/alethe_proof_rule.h"

namespace cvc5 {

namespace proof {

AletheProofPrinter::AletheProofPrinter()
{
  nested_level = 0;
  step_id = 1;
  prefix = "";
  assumptions.push_back({});
  steps.push_back({});
}

void AletheProofPrinter::alethePrinter(std::ostream& out,
                                       std::shared_ptr<ProofNode> pfn)
{
  Trace("alethe-printer") << "- Print proof in Alethe format. " << std::endl;

  // Special handling for the first scope
  // Print assumptions and add them to the list but do not print anchor.
  for (unsigned long int i = 3, size = pfn->getArguments().size(); i < size;
       i++)
  {
    Trace("alethe-printer")
        << "... print assumption " << pfn->getArguments()[i] << std::endl;
    out << "(assume a" << std::to_string(i - 3) << " " << pfn->getArguments()[i]
        << ")\n";
    assumptions[0][pfn->getArguments()[i]] = i - 3;
  }

  // Then, print the rest of the proof node
  alethePrinterInternal(out, pfn->getChildren()[0]);
}

std::string AletheProofPrinter::alethePrinterInternal(
    std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  // Store current id in case a subproof overwrites step_id
  int current_step_id = step_id;

  // If the proof node is untranslated a problem might have occured during
  // postprocessing
  if (pfn->getArguments().size() < 3 || pfn->getRule() != PfRule::ALETHE_RULE)
  {
    Trace("alethe-printer")
        << "... printing failed! Encountered untranslated Node. "
        << pfn->getResult() << " " << toString(pfn->getRule()) << " "
        << " / " << pfn->getArguments() << std::endl;
    return "";
  }

  // Get the alethe proof rule
  AletheRule vrule =
      static_cast<AletheRule>(std::stoul(pfn->getArguments()[0].toString()));

  // In case the rule is an anchor it is printed before its children. The
  // arguments of the anchor are printed as assumptions
  if (vrule == AletheRule::ANCHOR_SUBPROOF || vrule == AletheRule::ANCHOR_BIND)
  {
    // Look up if subproof has already been printed
    auto it = steps[nested_level].find(pfn->getArguments()[2]);
    if (it != steps[nested_level].end())
    {
      Trace("alethe-printer")
          << "... subproof is already printed " << pfn->getResult() << " "
          << vrule << " / " << pfn->getArguments() << std::endl;
      return prefix + "t" + std::to_string(it->second);
    }

    // If not printed before, enter next level
    nested_level++;
    assumptions.push_back({});
    steps.push_back({});

    // Print anchor
    Trace("alethe-printer")
        << "... print anchor " << pfn->getResult() << " " << vrule << " "
        << " / " << pfn->getArguments() << std::endl;
    out << "(anchor :step " << prefix << "t" << step_id;  // << " :args (";
    if (vrule == AletheRule::ANCHOR_BIND)
    {
      out << " :args (";
      for (unsigned long int j = 3, size = pfn->getArguments().size(); j < size;
           j++)
      {
        out << "(:= (" << pfn->getArguments()[j][0].toString() << " "
            << pfn->getArguments()[j][0].getType().toString() << ") "
            << pfn->getArguments()[j][1].toString() << ")";
        if (j != pfn->getArguments().size() - 1)
        {
          out << " ";
        }
      }
      out << ")";
    }
    out << ")\n";

    // Append index of anchor to prefix so that all steps in the subproof use it
    prefix.append("t" + std::to_string(step_id) + ".");
    step_id++;

    // Print assumptions
    if (vrule == AletheRule::ANCHOR_SUBPROOF)
    {
      for (unsigned long int i = 3, size = pfn->getArguments().size(); i < size;
           i++)
      {
        Trace("alethe-printer")
            << "... print assumption " << pfn->getArguments()[i] << std::endl;
        out << "(assume " << prefix << "a" << std::to_string(i - 3) << " "
            << pfn->getArguments()[i] << ")\n";
        assumptions[nested_level][pfn->getArguments()[i]] = i - 3;
      }
    }

    // Store step_id until children are printed to resume counter at current
    // position
    current_step_id = step_id;
    step_id = 1;
  }

  // Assumptions are printed at the anchor and therefore have to be in the list
  // of assumptions when an assume is reached
  if (vrule == AletheRule::ASSUME)
  {
    Trace("alethe-printer")
        << "... reached assumption " << pfn->getResult() << " " << vrule << " "
        << " / " << pfn->getArguments() << std::endl;

    auto it = assumptions[nested_level].find(pfn->getArguments()[2]);

    if (it != assumptions[nested_level].end())
    {
      Trace("alethe-printer")
          << "... search assumption in list " << pfn->getArguments()[2] << "/"
          << assumptions[nested_level] << std::endl;
      return prefix + "a" + std::to_string(it->second);
    }
    // temp, hotfix
    auto prefix2 = prefix;
    for (int i = nested_level; i >= 0; i--)
    {
      auto it = assumptions[i].find(pfn->getArguments()[2]);
      prefix2 = prefix2.substr(0, prefix2.find_last_of("."));
      Trace("alethe-printer") << prefix2 << std::endl;
      prefix2 = prefix2.substr(0, prefix2.find_last_of(".") + 1);
      Trace("alethe-printer") << prefix2 << std::endl;

      if (it != assumptions[i].end())
      {
        Trace("alethe-printer")
            << "... search assumption in list on level " << i << ": "
            << pfn->getArguments()[2] << "/" << assumptions[i] << "     "
            << prefix2 << std::endl;
        return prefix2 + "a" + std::to_string(it->second);
      }
    }

    // temp, hotfix
    for (int i = nested_level; i >= 0; i--)
    {
      auto prefix2 = prefix;
      auto it = assumptions[i].find(pfn->getArguments()[2]);
      if (it != assumptions[i].end())
      {
        Trace("alethe-printer")
            << "... search assumption in list on level " << i << ": "
            << pfn->getArguments()[2] << "/" << assumptions[i] << "     "
            << prefix2 << std::endl;
        prefix2 = prefix2.substr(0, prefix2.find_last_of("."));
        Trace("alethe-printer") << prefix2 << std::endl;
        prefix2 = prefix2.substr(0, prefix2.find_last_of(".") + 1);
        Trace("alethe-printer") << prefix2 << std::endl;
        return prefix2 + "a" + std::to_string(it->second);
      }
    }
    Trace("alethe-printer") << "... printing failed! Encountered assumption "
                               "that has not been printed! "
                            << pfn->getArguments()[2] << "/"
                            << assumptions[nested_level] << std::endl;
    return "";
  }

  // Print children
  std::vector<std::string> child_prefixes;
  for (auto child : pfn->getChildren())
  {
    child_prefixes.push_back(alethePrinterInternal(out, child));
  }

  // If rule is REORDER the rule should not be printed for now since they cannot
  // be reconstructed in Isabelle yet.
  /*if (vrule == AletheRule::REORDER)
  {
    Trace("alethe-printer")
        << "... skip reordering " << pfn->getResult() << " "
        << vrule << " / " << pfn->getArguments() << std::endl;
    return child_prefixes[0];
  }*/

  // If the rule is a subproof a subproof step needs to be printed
  if (vrule == AletheRule::ANCHOR_SUBPROOF || vrule == AletheRule::ANCHOR_BIND)
  {
    Trace("alethe-printer")
        << "... print node " << pfn->getResult() << " " << vrule << " / "
        << pfn->getArguments() << std::endl;

    prefix.pop_back();  // Remove last .
    // print subproof or bind
    out << "(step " << prefix << " " << pfn->getArguments()[2] << " :rule "
        << vrule;
    // Discharge assumptions
    // It is not clear from the onomicon whether the assumptions should be
    // discharged in this way or not.
    if (vrule == AletheRule::ANCHOR_SUBPROOF)
    {
      out << " :discharge (";
      for (unsigned long int j = 0; j < assumptions[nested_level].size(); j++)
      {
        out << prefix << ".a" + std::to_string(j);
        if (j != assumptions[nested_level].size() - 1)
        {
          out << " ";
        }
      }
      out << ")";
    }
    out << ")\n";

    // Set counters back to their old value before subproof was entered
    nested_level--;
    assumptions.pop_back();
    steps.pop_back();
    step_id = current_step_id;
    std::string current_t = prefix;
    prefix = prefix.substr(0, prefix.find_last_of("t"));
    return current_t;
  }

  // If the current step is already printed return its id
  auto it = steps[nested_level].find(pfn->getArguments()[2]);

  if (it != steps[nested_level].end())
  {
    Trace("alethe-printer")
        << "... step is already printed " << pfn->getResult() << " " << vrule
        << " / " << pfn->getArguments() << std::endl;
    return prefix + "t" + std::to_string(it->second);
  }

  // Print current step
  Trace("alethe-printer") << "... print node " << pfn->getResult() << " "
                          << vrule << " / " << pfn->getArguments() << std::endl;
  std::string current_t;
  current_t = "t" + std::to_string(step_id);
  steps[nested_level][pfn->getArguments()[2]] = step_id;
  out << "(step " << prefix << current_t << " ";
  out << pfn->getArguments()[2].toString() << " :rule " << vrule;
  if (pfn->getArguments().size() > 3)
  {
    out << " :args (";
    for (unsigned long int i = 3, size = pfn->getArguments().size(); i < size;
         i++)
    {
      if (vrule == AletheRule::FORALL_INST)
      {
        out << "(:= " << pfn->getArguments()[i][1].toString() << " "
            << pfn->getArguments()[i][0].toString() << ")";
      }
      else
      {
        out << pfn->getArguments()[i].toString();
      }
      if (i != pfn->getArguments().size() - 1)
      {
        out << " ";
      }
    }
    out << ")";
  }
  if (pfn->getChildren().size() >= 1)
  {
    out << " :premises (";
    for (unsigned long int i = 0, size = child_prefixes.size(); i < size; i++)
    {
      out << child_prefixes[i];
      if (i != child_prefixes.size() - 1)
      {
        out << " ";
      }
    }
    out << "))\n";
  }
  else
  {
    out << ")\n";
  }
  ++step_id;
  return prefix + current_t;
}

}  // namespace proof

}  // namespace cvc5
