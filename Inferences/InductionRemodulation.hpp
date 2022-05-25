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

#include "Lib/SharedSet.hpp"

namespace Inferences
{

inline Term* getPointedTerm(Term* t) {
  if (!env.signature->getFunction(t->functor())->pointer()) {
    return t;
  }
  auto ptr = t->getPointedTerm();
#if VDEBUG
  if (ptr != t) {
    NonVariableIterator nvi(ptr);
    while (nvi.hasNext()) {
      auto st = nvi.next().term();
      ASS_REP(!env.signature->getFunction(st->functor())->pointer(),t->toString());
    }
  }
#endif
  return ptr;
}

class PointedTermIterator
  : public IteratorCore<TermList>
{
public:
  PointedTermIterator(Literal* lit)
  : _stack(8),
    _added(0)
  {
    CALL("PointedTermIterator::PointedTermIterator");
    _stack.push(getPointedTerm(lit));
    PointedTermIterator::next();
  }

  bool hasNext() override { return !_stack.isEmpty(); }
  TermList next() override;
  void right();

private:
  Stack<Term*> _stack;
  int _added;
};

class PointerTermReplacement : public TermTransformer {
private:
  TermList transformSubterm(TermList trm) override {
    if (trm.isVar()) {
      return trm;
    }
    return TermList(getPointedTerm(trm.term()));
  }
};

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

inline bool litHasAllVarsOfClause(Literal* lit, Clause* cl) {
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
     isFormulaTransformation(cl->inference().rule()));
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
    ASS_EQ(_o, getPointedTerm(_o));
    ASS_EQ(_r.term(), getPointedTerm(_r.term()));
    _occurrences = _lit->countSubtermOccurrences(TermList(_o));
    NonVariableIterator nvi(_lit);
    while (nvi.hasNext()) {
      auto t = nvi.next().term();
      auto ptr = getPointedTerm(t);
      if (t != ptr) {
        _occurrences += ptr->countSubtermOccurrences(TermList(_o));
      }
    }
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
    Replacer(Term* o, TermList r, unsigned i, bool replaceWithPointer = true)
      : _o(o), _r(r), _i(i), _matchCount(0), _replaceWithPointer(replaceWithPointer) {}

private:
    TermList transformSubterm(TermList trm) override;

    Term* _o;
    TermList _r;
    unsigned _i;
    unsigned _matchCount;
    bool _replaceWithPointer;
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
  ClauseIterator perform(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult);
private:
  RemodulationLHSIndex* _lhsIndex;
  RemodulationSubtermIndex* _termIndex;
};

}

#endif /*__InductionRemodulation__*/
