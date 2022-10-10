/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file VacuousnessChecker.hpp
 * Defines class VacuousnessChecker
 *
 */

#ifndef __VacuousnessChecker__
#define __VacuousnessChecker__

#include <cmath>

#include "Forwards.hpp"

// #include "Saturation/MiniSaturation.hpp"

#include "Indexing/CodeTreeInterfaces.hpp"
#include "Indexing/InductionFormulaIndex.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/TermIndex.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

#include "Kernel/Problem.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Kernel/Theory.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/List.hpp"

namespace Inferences
{

struct InductionContext;
class InductionClauseIterator;

namespace InductiveReasoning
{

class VacuousnessChecker
{
public:
  VacuousnessChecker(InductionFormulaIndex& formulaIndex)
      : _salg(nullptr), _formulaIndex(formulaIndex), _delayedIndex(), _delayedLitIndex(),
        _lhsIndex(nullptr), _literalIndex(nullptr)/* , _ms(nullptr) */ {}

  void attach(SaturationAlgorithm* salg);
  void detach();

  bool maybeDelayInduction(const InductionContext& ctx, InductionFormulaIndex::Entry* e);
  void checkForDelayedInductions(Literal* lit, Clause* cl, InductionClauseIterator& clIt);
  bool checkForVacuousness(const InductionContext& ctx, InductionFormulaIndex::Entry* e);
  // void initMiniSaturation();
  // void addClausesToMiniSaturation(const ClauseStack& cls);
  // bool runMiniSaturation();

private:
  bool checkForVacuousness(Literal* lit, Term* t);

  SaturationAlgorithm* _salg;
  InductionFormulaIndex& _formulaIndex;
  TermSubstitutionTree _delayedIndex;
  LiteralSubstitutionTree _delayedLitIndex;
  InductionLHSIndex* _lhsIndex;
  InductionLiteralIndex* _literalIndex;
  // MiniSaturation* _ms;
};

}

}

#endif /*__VacuousnessChecker__*/
