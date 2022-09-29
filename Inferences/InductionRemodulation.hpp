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
 * @file InductionRemodulation.hpp
 * Defines class InductionRemodulation
 *
 */

#ifndef __InductionRemodulation__
#define __InductionRemodulation__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "InductionHelper.hpp"

#include "Kernel/EqHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"

#include "Lib/ScopedPtr.hpp"
#include "Lib/SharedSet.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

inline bool canUseForRewrite(Literal* lit, Clause* cl) {
  if (lit->isNegative() || !lit->isEquality()) {
    return false;
  }
  auto vit = cl->getVariableIterator();
  while (vit.hasNext()) {
    auto v = vit.next();
    if (!lit->containsSubterm(TermList(v, false))) {
      return false;
    }
  }
  return true;
}

inline bool termHasAllVarsOfClause(TermList t, Clause* cl) {
  auto vit = cl->getVariableIterator();
  while (vit.hasNext()) {
    auto v = vit.next();
    if (!t.containsSubterm(TermList(v, false))) {
      return false;
    }
  }
  return true;
}

inline bool canUseForRewrite(Clause* cl) {
  return cl->length() == 1 ||
    (env.options->inductionConsequenceGeneration() == Options::InductionConsequenceGeneration::ON &&
     isFormulaTransformation(cl->inference().rule())) ||
    cl->inference().rule() == Kernel::InferenceRule::INDUCTION_FORWARD_REWRITING ||
    cl->inference().rule() == Kernel::InferenceRule::INDUCTION_REMODULATION;
}

inline bool hasTermToInductOn(Term* t, Literal* l) {
  static const bool intInd = InductionHelper::isIntInductionOn();
  static const bool structInd = InductionHelper::isStructInductionOn();
  NonVariableIterator stit(t);
  while (stit.hasNext()) {
    auto st = stit.next();
    if (InductionHelper::isInductionTermFunctor(st.term()->functor()) &&
      ((structInd && InductionHelper::isStructInductionFunctor(st.term()->functor())) ||
       (intInd && InductionHelper::isIntInductionTermListInLiteral(st, l))))
    {
      return true;
    }
  }
  return false;
}

class SingleOccurrenceReplacementIterator : public IteratorCore<Literal*> {
public:
  CLASS_NAME(SingleOccurrenceReplacementIterator);
  USE_ALLOCATOR(SingleOccurrenceReplacementIterator);
  SingleOccurrenceReplacementIterator(Literal* lit, Term* o, TermList r)
      : _lit(lit), _o(o), _r(r)
  {
    _occurrences = _lit->countSubtermOccurrences(TermList(_o));
  }

  bool hasNext() override {
    return _iteration < _occurrences;
  }
  Literal* next() override;

private:
  unsigned _iteration = 0;
  unsigned _occurrences;
  Literal* _lit;
  Term* _o;
  TermList _r;

  class Replacer : public TermTransformer {
  public:
    Replacer(Term* o, TermList r, unsigned i)
      : _o(o), _r(r), _i(i), _matchCount(0) {}

  private:
    TermList transformSubterm(TermList trm) override;

    Term* _o;
    TermList _r;
    unsigned _i;
    unsigned _matchCount;
  };
};

class InductionRemodulation
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InductionRemodulation);
  USE_ALLOCATOR(InductionRemodulation);

  InductionRemodulation()
    : _lhsIndex(), _termIndex() {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  ClauseIterator generateClauses(Clause* premise) override;
private:
  ClauseIterator perform(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult);

  RemodulationLHSIndex* _lhsIndex;
  RemodulationSubtermIndex* _termIndex;
};

class InductionSGIWrapper
: public SimplifyingGeneratingInference
{
public:
  CLASS_NAME(InductionSGIWrapper);
  USE_ALLOCATOR(InductionSGIWrapper);

  InductionSGIWrapper(GeneratingInferenceEngine* induction,
      GeneratingInferenceEngine* inductionRemodulation,
      SimplifyingGeneratingInference* generator)
    : _induction(induction), _inductionRemodulation(inductionRemodulation), _generator(generator) {}

  ClauseGenerationResult generateSimplify(Clause* premise) override {
    if (!premise->isInductionClause()) {
      return _generator->generateSimplify(premise);
    }
    return ClauseGenerationResult {
      .clauses = pvi(getConcatenatedIterator(
        _induction->generateClauses(premise),
        _inductionRemodulation->generateClauses(premise))),
      .premiseRedundant = false,
    };
  }
  void attach(SaturationAlgorithm* salg) override
  {
    _generator->attach(salg);
  }
  void detach() override
  {
    _generator->detach();
  }
private:
  GeneratingInferenceEngine* _induction;
  GeneratingInferenceEngine* _inductionRemodulation;
  ScopedPtr<SimplifyingGeneratingInference> _generator;
};

}

#endif /*__InductionRemodulation__*/
