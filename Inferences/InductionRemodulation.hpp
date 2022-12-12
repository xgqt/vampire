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

inline void selectLiterals(Clause* c) {
  unsigned sel = 0;
  for (unsigned i = 0; i < c->length(); i++) {
    auto& cur = (*c)[i];
    if (cur->isEquality()) {
      swap((*c)[sel],cur);
      sel++;
    }
  }
  c->setSelected(sel);
}

inline bool termHasAllVarsOfClause(TermList t, Clause* cl) {
  return iterTraits(cl->getVariableIterator())
    .all([&t](unsigned v) {
      return t.containsSubterm(TermList(v, false));
    });
}

inline bool termAlgebraFunctor(unsigned functor) {
  auto sym = env.signature->getFunction(functor);
  return sym->termAlgebraCons() || sym->termAlgebraDest();
}

inline bool hasTermToInductOn(Term* t, Literal* l) {
  static const bool intInd = InductionHelper::isIntInductionOn();
  static const bool structInd = InductionHelper::isStructInductionOn();
  NonVariableIterator stit(t);
  while (stit.hasNext()) {
    auto st = stit.next();
    if (InductionHelper::isInductionTermFunctor(st.term()->functor()) &&
      ((structInd && !termAlgebraFunctor(st.term()->functor()) && InductionHelper::isStructInductionFunctor(st.term()->functor())) ||
       (intInd && InductionHelper::isIntInductionTermListInLiteral(st, l))))
    {
      return true;
    }
  }
  return false;
}

inline bool shouldRewriteEquality(Literal* lit, Clause* cl, Ordering& ord) {
  return iterTraits(EqHelper::getLHSIterator(lit,ord))
    .any([lit](TermList side) {
      return side.isTerm() && !hasTermToInductOn(side.term(),lit);
    });
}

class SingleOccurrenceReplacementIterator : public IteratorCore<Literal*> {
public:
  CLASS_NAME(SingleOccurrenceReplacementIterator);
  USE_ALLOCATOR(SingleOccurrenceReplacementIterator);
  SingleOccurrenceReplacementIterator(Literal* lit, Term* o, TermList r)
      : _lit(lit), _o(o), _r(r), _occurrences(_lit->countSubtermOccurrences(TermList(_o))) {}

  bool hasNext() override {
    return _iteration < _occurrences;
  }
  Literal* next() override;

private:
  unsigned _iteration = 0;
  Literal* _lit;
  Term* _o;
  TermList _r;
  unsigned _occurrences;

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

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  ClauseIterator generateClauses(Clause* premise) override;
  void output();
private:
  ClauseIterator perform(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult);

  RemodulationLHSIndex* _lhsIndex;
  RemodulationSubtermIndex* _termIndex;
  DHMap<Clause*, unsigned> _eqs;
  DemodulationLHSIndex* _demLhsIndex;
};

class InductionForwardRewriting;

class InductionSGIWrapper
: public SimplifyingGeneratingInference
{
public:
  CLASS_NAME(InductionSGIWrapper);
  USE_ALLOCATOR(InductionSGIWrapper);

  InductionSGIWrapper(GeneratingInferenceEngine* induction,
      InductionRemodulation* inductionRemodulation,
      InductionForwardRewriting* inductionForwardRewriting,
      SimplifyingGeneratingInference* generator)
    : _induction(induction), _inductionRemodulation(inductionRemodulation),
      _inductionForwardRewriting(inductionForwardRewriting), _generator(generator) {}

  ClauseGenerationResult generateSimplify(Clause* premise) override;

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
  InductionRemodulation* _inductionRemodulation;
  InductionForwardRewriting* _inductionForwardRewriting;
  ScopedPtr<SimplifyingGeneratingInference> _generator;
};

}

#endif /*__InductionRemodulation__*/
