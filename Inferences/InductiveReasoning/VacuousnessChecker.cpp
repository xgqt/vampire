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
 * @file VacuousnessChecker.cpp
 * Implements class VacuousnessChecker.
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

#include "VacuousnessChecker.hpp"
#include "Inferences/Induction.hpp"

using std::pair;
using std::make_pair;

namespace Inferences
{

namespace InductiveReasoning
{
using namespace Kernel;
using namespace Lib; 

void VacuousnessChecker::attach(SaturationAlgorithm* salg)
{
  CALL("VacuousnessChecker::attach");

  _salg = salg;
  _lhsIndex = static_cast<InductionLHSIndex*>(salg->getIndexManager()->request(INDUCTION_LHS_INDEX));
  _literalIndex = static_cast<InductionLiteralIndex*>(salg->getIndexManager()->request(INDUCTION_LITERAL_INDEX));
}

void VacuousnessChecker::detach()
{
  CALL("VacuousnessChecker::detach");

  _salg->getIndexManager()->release(INDUCTION_LITERAL_INDEX);
  _literalIndex = nullptr;
  _salg->getIndexManager()->release(INDUCTION_LHS_INDEX);
  _lhsIndex = nullptr;
  _salg = nullptr;
}

inline void updatePositions(TermList tt, Stack<unsigned>& pos, TermAlgebra* ta, InductionFormulaIndex::Entry* e, Clause* cl) {
  if (!tt.isTerm()) {
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

bool VacuousnessChecker::maybeDelayInduction(const InductionContext& ctx, InductionFormulaIndex::Entry* e)
{
  CALL("VacuousnessChecker::maybeDelayInduction");
  TIME_TRACE("forward delayed induction");
  if (e->_delayed) {
    env.statistics->delayedInductionApplications++;
    e->_delayedApplications.push(ctx);
    return false;
  }
  if (!e->_delayed && e->_activatingClauses.size()) {
    return true;
  }
  TermList sort = SortHelper::getResultSort(ctx._indTerm);
  if (!env.signature->isTermAlgebraSort(sort)) {
    return true;
  }
  auto ta = env.signature->getTermAlgebraOfSort(sort);
  Stack<unsigned> pos;
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    e->_activatingClauses.push(nullptr);
    pos.push(i);
  }
  bool found = false;
  TermList x(0,false);
  TermReplacement tr(getPlaceholderForTerm(ctx._indTerm), x);
  auto tlit = tr.transform(ctx._cls.begin()->second[0]);
  NonVariableNonTypeIterator it(tlit);
  DHSet<Term*> tried;
  while (it.hasNext() && pos.isNonEmpty()) {
    TIME_TRACE("forward delayed induction subterm loop");
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
    TIME_TRACE("forward delayed induction literal check");
    auto uit = getConcatenatedIterator(_literalIndex->getUnifications(tlit, true), _literalIndex->getUnifications(tlit, false));
    // TODO consider only complmentary literals
    // auto uit = _literalIndex->getUnifications(tlit, true);
    while (uit.hasNext() && pos.isNonEmpty()) {
      auto qr = uit.next();
      auto tt = qr.substitution->applyToQuery(x);
      updatePositions(tt, pos, ta, e, qr.clause);
    }
  }
  if (pos.isNonEmpty()) {
    e->_delayed = true;
    e->_delayedApplications.push(ctx);
    env.statistics->delayedInductions++;
    env.statistics->delayedInductionApplications++;
    NonVariableNonTypeIterator it(tlit);
    while (it.hasNext()) {
      auto t = it.next();
      if (!t.containsSubterm(x)) {
        it.right();
        continue;
      }
      _delayedIndex.insert(t, tlit, nullptr);
    }
    _delayedLitIndex.insert(tlit, nullptr);
    return false;
  }
  return true;
}

void VacuousnessChecker::checkForDelayedInductions(Literal* lit, Clause* cl, InductionClauseIterator& clIt)
{
  CALL("VacuousnessChecker::checkForDelayedInductions");
  TIME_TRACE("backward delayed induction");
  TermList x(0,false);
  vset<Literal*> toBeRemoved;
  auto reactivate = [&toBeRemoved, this, cl, &clIt](TermList t, Literal* lit){
    TIME_TRACE("backward delayed induction reactivate");
    if (!t.isTerm() || toBeRemoved.count(lit)) {
      return;
    }
    TermList sort = SortHelper::getResultSort(t.term());
    if (!env.signature->isTermAlgebraSort(sort)) {
      return;
    }
    auto ta = env.signature->getTermAlgebraOfSort(sort);
    auto ph = getPlaceholderForTerm(t.term());
    Substitution subst;
    subst.bind(0, ph);
    // dummy context just to get the entry from the induction formula index
    InductionContext dummy(ph, lit->apply(subst), nullptr);
    InductionFormulaIndex::Entry* e = _formulaIndex.find(dummy);
    ASS(e);
    ASS(e->_delayed);
    ASS(e->_delayedApplications.isNonEmpty());
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
      return;
    }
    clIt.generateStructuralFormulas(dummy, e);
    ASS_NEQ(0,env.statistics->delayedInductions);
    env.statistics->delayedInductions--;
    TIME_TRACE("backward delayed induction resolution");
    while (e->_delayedApplications.isNonEmpty()) {
      auto ctx = e->_delayedApplications.pop();
      ASS_NEQ(0,env.statistics->delayedInductionApplications);
      env.statistics->delayedInductionApplications--;
      for (auto& kv : e->get()) {
        clIt.resolveClauses(kv.first, ctx, kv.second);
      }
    }
    e->_delayed = false;
    toBeRemoved.insert(lit);
  };

  if (lit->isEquality()) {
    if (lit->isPositive()) {
      TIME_TRACE("backward delayed induction subterm loop");
      for (unsigned j=0; j<2; j++) {
        auto side = *lit->nthArgument(j);
        if (side.isVar() || !termAlgebraConsCheck(side.term())) {
          continue;
        }
        auto qrit = _delayedIndex.getUnifications(side,true);
        while (qrit.hasNext()) {
          auto qr = qrit.next();
          auto tt = qr.substitution->applyToResult(x);
          reactivate(tt, qr.literal);
        }
      }
    }
  } else if (termAlgebraConsCheck(lit)) {
    TIME_TRACE("backward delayed induction literal check");
    auto qrit = getConcatenatedIterator(_delayedLitIndex.getUnifications(lit, true, true), _delayedLitIndex.getUnifications(lit, false, true));
    // TODO consider only complmentary literals
    // auto qrit = _delayedLitIndex.getUnifications(lit, true, true);
    while (qrit.hasNext()) {
      auto qr = qrit.next();
      auto tt = qr.substitution->applyToResult(x);
      reactivate(tt, qr.literal);
    }
  }
  for (const auto& lit : toBeRemoved) {
    NonVariableNonTypeIterator it(lit);
    _delayedLitIndex.remove(lit, nullptr);
    while (it.hasNext()) {
      auto t = it.next();
      if (!t.containsSubterm(x)) {
        it.right();
        continue;
      }
      _delayedIndex.remove(t, lit, nullptr);
    }
  }
}

bool onlyCtorsDownToTerm(Term* t, Term* st) {
  Stack<Term*> todo;
  todo.push(t);
  while (todo.isNonEmpty()) {
    auto curr = todo.pop();
    if (curr == st) {
      return true;
    }
    if (!curr->containsSubterm(TermList(st))) {
      continue;
    }
    if (env.signature->getFunction(curr->functor())->termAlgebraCons()) {
      for (unsigned i = 0; i < curr->arity(); i++) {
        todo.push(curr->nthArgument(i)->term());
      }
    }
  }
  return false;
}

bool monotonicityCheck(Term* lhs, Term* rhs) {
  Stack<pair<Term*,Term*>> todo;
  todo.push(make_pair(lhs,rhs));
  while (todo.isNonEmpty()) {
    auto p = todo.pop();
    if (p.first == p.second) {
      continue;
    }
    auto lf = p.first->functor();
    auto rf = p.second->functor();
    if (lf == rf) {
      for (unsigned i = 0; i < p.first->arity(); i++) {
        todo.push(make_pair(p.first->nthArgument(i)->term(), p.second->nthArgument(i)->term()));
      }
    } else {
      if (p.first->containsSubterm(TermList(p.second))) {
        if (onlyCtorsDownToTerm(p.first, p.second)) {
          continue;
        }
      } else if (p.second->containsSubterm(TermList(p.first))) {
        if (onlyCtorsDownToTerm(p.second, p.first)) {
          continue;
        }
      }
      return false;
    }
  }
  return true;
}

bool VacuousnessChecker::checkForVacuousness(Literal* lit, Term* t)
{
  CALL("VacuousnessChecker::checkForVacuousness");
  if (!lit->isEquality() || lit->isPositive()) {
    return true;
  }
  auto lhs = lit->nthArgument(0)->term();
  auto rhs = lit->nthArgument(1)->term();
  auto lhsc = lhs->containsSubterm(TermList(t));
  if (!lhsc || !rhs->containsSubterm(TermList(t))) {
    auto side = lhsc ? lhs : rhs;
    NonVariableIterator sti(side,true);
    while (sti.hasNext()) {
      auto st = sti.next();
      if (st == TermList(t)) {
        continue;
      }
      auto sym = env.signature->getFunction(st.term()->functor());
      if (sym->termAlgebraCons() || sym->termAlgebraDest() || sym->nonErasing()) {
        continue;
      }
      if (st.containsSubterm(TermList(t))) {
        return true;
      }
    }
    env.statistics->vacuousInductionFormulaDiscardedStaticallyOneSide++;
    return false;
  } else {
    if (lhs == t || rhs == t) {
      auto symb = env.signature->getFunction((lhs == t) ? rhs->functor() : lhs->functor());
      if (symb->termAlgebraCons()) {
        env.statistics->vacuousInductionFormulaDiscardedStaticallyMismatch++;
        return false;
      }
    }
    if (monotonicityCheck(lhs, rhs)) {
      env.statistics->vacuousInductionFormulaDiscardedStaticallyMonotonicity++;
      return false;
    }
  }

  return true;
}

// returns true if the context is vacuous by these checks
// TODO enable check for more complex conclusions
// TODO add check that the induction term datatype contains at least two ctors
bool VacuousnessChecker::check(const InductionContext& ctx, InductionFormulaIndex::Entry* e)
{
  CALL("VacuousnessChecker::check");
  // don't check any non-unit inductions for now
  if (ctx._cls.size() != 1 || ctx._cls.begin()->second.size() != 1) {
    return true;
  }

  // context is vacuous if all of these conditions hold:
  // * context contains only one negative equality
  // * only one side contains the induction term 
  // * there is an occurrence of the induction term
  //   which has only term algebra ctor/dtor superterms
  auto lit = ctx._cls.begin()->second[0];
  auto ph = getPlaceholderForTerm(ctx._indTerm);
  TermReplacement tr(ph, TermList(0,false));
  // if (_formulaIndex.isVacuous(tr.transform(ctx._cls.begin()->second[0]))) {
  //   env.statistics->vacuousInductionFormulaDiscardedDynamically2++;
  //   _formulaIndex.makeVacuous(ctx, e);
  //   return false;
  // }
  if (!checkForVacuousness(lit, ph)) {
    e->_vacuous = true;
    env.statistics->vacuousInductionFormulaDiscardedStatically++;
    return false;
  }

  return maybeDelayInduction(ctx, e);
}

bool VacuousnessChecker::termAlgebraConsCheck(Term* t)
{
  CALL("VacuousnessChecker::termAlgebraConsCheck");
  NonVariableNonTypeIterator nvi(t);
  while (nvi.hasNext()) {
    auto t = nvi.next().term();
    auto f = t->functor();
    if (!env.signature->getFunction(f)->termAlgebraCons()) {
      continue;
    }
    Set<unsigned> vars;
    for (unsigned j = 0; j < t->arity(); j++) {
      if (t->nthArgument(j)->isVar()) {
        vars.insert(t->nthArgument(j)->var());
      }
    }
    if (vars.size() == t->arity()) {
      return true;
    }
  }
  return false;
}

}

}
