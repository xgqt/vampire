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
 * @file InductionPostponement.cpp
 * Implements class InductionPostponement.
 */

#include <utility>

#include "Indexing/IndexManager.hpp"

#include "Lib/BitUtils.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/Set.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "InductionPostponement.hpp"
#include "Inferences/Induction.hpp"

using std::pair;
using std::make_pair;

namespace Inferences
{

namespace InductiveReasoning
{
using namespace Kernel;
using namespace Lib; 

void InductionPostponement::attach(SaturationAlgorithm* salg)
{
  CALL("InductionPostponement::attach");

  _salg = salg;
  _lhsIndex = static_cast<TermIndex*>(salg->getIndexManager()->request(GENERAL_LHS_INDEX));
  _literalIndex = static_cast<LiteralIndex*>(salg->getIndexManager()->request(BACKWARD_SUBSUMPTION_SUBST_TREE));
}

void InductionPostponement::detach()
{
  CALL("InductionPostponement::detach");

  _salg->getIndexManager()->release(BACKWARD_SUBSUMPTION_SUBST_TREE);
  _literalIndex = nullptr;
  _salg->getIndexManager()->release(GENERAL_LHS_INDEX);
  _lhsIndex = nullptr;
  _salg = nullptr;
}

inline void updatePositions(TermList tt, Stack<unsigned>& pos, TermAlgebra* ta, InductionFormulaIndex::Entry* e, Clause* cl) {
  if (!tt.isTerm()) {
    return;
  }
  auto t = tt.term();
  if (!env.signature->getFunction(t->functor())->termAlgebraCons()) {
    return;
  }
  for (unsigned i = 0; i < pos.size(); i++) {
    if (tt.term()->functor() != ta->constructor(pos[i])->functor()) {
      continue;
    }
    Set<unsigned> vars;
    for (unsigned j = 0; j < tt.term()->arity(); j++) {
      if (tt.term()->nthArgument(j)->isVar()) {
        vars.insert(tt.term()->nthArgument(j)->var());
      }
    }
    if (vars.size() == tt.term()->arity()) {
      ASS_EQ(e->_activatingClauses[pos[i]], nullptr);
      e->_activatingClauses[pos[i]] = cl;
      swap(pos[i],pos.top());
      pos.pop();
      break;
    }
  }
}

// returns true if the induction is postponed
bool InductionPostponement::maybePostpone(const InductionContext& ctx, InductionFormulaIndex::Entry* e)
{
  CALL("InductionPostponement::maybePostpone");
  TIME_TRACE("forward induction postponement");
  // this induction is already postponed
  if (e->_postponed) {
    return true;
  }
  // if not postponed but this field is initialized,
  // then the induction was reactivated already
  if (e->_activatingClauses.size()) {
    return false;
  }
  TermList sort = SortHelper::getResultSort(ctx._indTerm);
  if (!env.signature->isTermAlgebraSort(sort)) {
    return false;
  }
  auto ta = env.signature->getTermAlgebraOfSort(sort);
  Stack<unsigned> pos;
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    e->_activatingClauses.push(nullptr);
    pos.push(i);
  }
  TermList x(0,false);
  DHSet<Term*> tried;
  TermReplacement tr(getPlaceholderForTerm(ctx._indTerm), x);
  for (const auto& kv : ctx._cls) {
    for (const auto& lit : kv.second) {
      auto tlit = tr.transform(lit);
      NonVariableNonTypeIterator it(tlit);
      while (it.hasNext() && pos.isNonEmpty()) {
        auto t = it.next();
        if (!t.containsSubterm(x) || !tried.insert(t.term())) {
          it.right();
          continue;
        }
        auto uit = _lhsIndex->getUnifications(t);
        while (uit.hasNext() && pos.isNonEmpty()) {
          auto qr = uit.next();
          auto tt = qr.substitution->applyToQuery(x);
          updatePositions(tt, pos, ta, e, qr.clause);
        }
      }
      if (pos.isNonEmpty() && !tlit->isEquality()) {
        auto uit = _literalIndex->getUnifications(tlit, true/*complementary*/);
        while (uit.hasNext() && pos.isNonEmpty()) {
          auto qr = uit.next();
          auto tt = qr.substitution->applyToQuery(x);
          updatePositions(tt, pos, ta, e, qr.clause);
        }
      }
    }
  }
  if (pos.isNonEmpty()) {
    e->_postponed = true;
    e->_postponedApplications.push(ctx);
    env.statistics->postponedInductions++;
    env.statistics->postponedInductionApplications++;
    for (const auto& kv : ctx._cls) {
      for (const auto& lit : kv.second) {
        Stack<InductionFormulaKey>* ks = nullptr;
        if (_literalMap.getValuePtr(lit, ks)) {
          auto tlit = tr.transform(lit);
          NonVariableNonTypeIterator it(tlit);
          while (it.hasNext()) {
            auto t = it.next();
            if (!t.containsSubterm(x)) {
              it.right();
              continue;
            }
            _postponedTermIndex.insert(t, tlit, nullptr);
          }
          _postponedLitIndex.insert(tlit, nullptr);
        }
        ASS(ks);
        ks->push(InductionFormulaIndex::represent(ctx));
      }
    }
    return true;
  }
  return false;
}

void InductionPostponement::checkForPostponedInductions(Literal* lit, Clause* cl, InductionClauseIterator& clIt)
{
  CALL("InductionPostponement::checkForPostponedInductions");
  TIME_TRACE("backward induction postponement");
  TermList x(0,false);
  DHMap<InductionFormulaKey,Term*> toBeRemoved;
  auto reactivate = [&toBeRemoved, this, cl, &clIt, &x](TermList t, Literal* lit){
    if (!t.isTerm()) {
      return;
    }
    TermList sort = SortHelper::getResultSort(t.term());
    if (!env.signature->isTermAlgebraSort(sort)) {
      return;
    }
    auto ta = env.signature->getTermAlgebraOfSort(sort);
    Substitution subst;
    subst.bind(x.var(), getPlaceholderForTerm(t.term()));
    auto ks = _literalMap.findPtr(lit->apply(subst));
    for (const auto& key : *ks) {
      if (toBeRemoved.find(key)) {
        continue;
      }
      auto e = _formulaIndex.findByKey(key);
      ASS(e);
      ASS(e->_postponed);
      ASS(e->_postponedApplications.isNonEmpty());
      ASS(!e->_vacuous);

      Stack<unsigned> pos;
      ASS_EQ(e->_activatingClauses.size(), ta->nConstructors());
      for (unsigned i = 0; i < ta->nConstructors(); i++) {
        if (!e->_activatingClauses[i]) {
          pos.push(i);
        }
      }
      updatePositions(t, pos, ta, e, cl);
      if (pos.isNonEmpty()) {
        continue;
      }
      // any of the postponed contexts suffices to generate the formulas
      auto ph = getPlaceholderForTerm(e->_postponedApplications[0]._indTerm);
      clIt.generateStructuralFormulas(e->_postponedApplications[0], e);
      ASS_NEQ(0,env.statistics->postponedInductions);
      env.statistics->postponedInductions--;
      while (e->_postponedApplications.isNonEmpty()) {
        auto ctx = e->_postponedApplications.pop();
        ASS_NEQ(0,env.statistics->postponedInductionApplications);
        env.statistics->postponedInductionApplications--;
        for (auto& kv : e->get()) {
          clIt.resolveClauses(kv.first, ctx, kv.second);
        }
      }
      e->_postponed = false;
      toBeRemoved.insert(key,ph);
    }
  };

  if (lit->isEquality()) {
    if (lit->isPositive()) {
      for (unsigned j=0; j<2; j++) {
        auto lhs = *lit->nthArgument(j);
        auto qrit = _postponedTermIndex.getUnifications(lhs,true);
        while (qrit.hasNext()) {
          auto qr = qrit.next();
          auto tt = qr.substitution->applyToResult(x);
          reactivate(tt, qr.literal);
        }
      }
    }
  } else {
    auto qrit = _postponedLitIndex.getUnifications(lit, true/*complementary*/, true);
    while (qrit.hasNext()) {
      auto qr = qrit.next();
      auto tt = qr.substitution->applyToResult(x);
      reactivate(tt, qr.literal);
    }
  }
  decltype(toBeRemoved)::Iterator rit(toBeRemoved);
  while (rit.hasNext()) {
    InductionFormulaKey key;
    Term* ph;
    rit.next(key,ph);
    for (const auto& lits : key.first) {
      for (const auto& lit : lits) {
        Stack<InductionFormulaKey>* ks = nullptr;
        ALWAYS(!_literalMap.getValuePtr(lit, ks));
        int i = -1;
        for (unsigned j = 0; j < ks->size(); j++) {
          if ((*ks)[j] == key) {
            ASS_L(i,0);
            i = j;
#if !VDEBUG
            break;
#endif
          }
        }
        ASS_GE(i,0);
        swap((*ks)[i],ks->top());
        ks->pop();
        if (ks->isEmpty()) {
          _literalMap.remove(lit);
          TermReplacement tr(ph, x);
          auto tlit = tr.transform(lit);
          _postponedLitIndex.remove(tlit, nullptr);
          NonVariableNonTypeIterator it(tlit);
          while (it.hasNext()) {
            auto t = it.next();
            if (!t.containsSubterm(x)) {
              it.right();
              continue;
            }
            _postponedTermIndex.remove(t, tlit, nullptr);
          }
        }
      }
    }
  }
}

}

}
