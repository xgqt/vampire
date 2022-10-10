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

#include "Indexing/InductionFormulaIndex.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

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
        _lhsIndex(nullptr), _literalIndex(nullptr) {}

  void attach(SaturationAlgorithm* salg);
  void detach();

  void checkForDelayedInductions(Literal* lit, Clause* cl, InductionClauseIterator& clIt);
  bool check(const InductionContext& ctx, InductionFormulaIndex::Entry* e);

  static bool termAlgebraConsCheck(Term* t);

private:
  bool maybeDelayInduction(const InductionContext& ctx, InductionFormulaIndex::Entry* e);
  bool checkForVacuousness(Literal* lit, Term* t);

  SaturationAlgorithm* _salg;
  InductionFormulaIndex& _formulaIndex;
  TermSubstitutionTree _delayedIndex;
  LiteralSubstitutionTree _delayedLitIndex;
  InductionLHSIndex* _lhsIndex;
  InductionLiteralIndex* _literalIndex;
};

}

}

#endif /*__VacuousnessChecker__*/
