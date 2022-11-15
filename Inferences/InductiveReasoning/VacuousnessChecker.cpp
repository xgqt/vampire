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

#include "VacuousnessChecker.hpp"
#include "Inferences/Induction.hpp"
#include "Shell/Statistics.hpp"

using std::pair;
using std::make_pair;

namespace Inferences
{

namespace InductiveReasoning
{
using namespace Kernel;
using namespace Lib; 

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

bool VacuousnessChecker::isVacuous(Literal* lit, Term* t)
{
  CALL("VacuousnessChecker::checkForVacuousness");
  if (!lit->isEquality() || lit->isPositive()) {
    return false;
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
        return false;
      }
    }
    env.statistics->vacuousInductionFormulaDiscardedStaticallyOneSide++;
    return true;
  } else {
    if (lhs == t || rhs == t) {
      auto symb = env.signature->getFunction((lhs == t) ? rhs->functor() : lhs->functor());
      if (symb->termAlgebraCons()) {
        env.statistics->vacuousInductionFormulaDiscardedStaticallyMismatch++;
        return true;
      }
    }
    if (monotonicityCheck(lhs, rhs)) {
      env.statistics->vacuousInductionFormulaDiscardedStaticallyMonotonicity++;
      return true;
    }
  }

  return false;
}

// returns true if the context is vacuous by these checks
// TODO enable check for more complex conclusions
// TODO add check that the induction term datatype contains at least two ctors
bool VacuousnessChecker::isVacuous(const InductionContext& ctx, InductionFormulaIndex::Entry* e)
{
  CALL("VacuousnessChecker::isVacuous");

  // don't check any non-unit inductions for now
  if (ctx._cls.size() != 1 || ctx._cls.begin()->second.size() != 1) {
    return false;
  }

  // context is vacuous if all of these conditions hold:
  // * context contains only one negative equality
  // * only one side contains the induction term 
  // * there is an occurrence of the induction term
  //   which has only term algebra ctor/dtor superterms
  auto lit = ctx._cls.begin()->second[0];
  auto ph = getPlaceholderForTerm(ctx._indTerm);
  // TermReplacement tr(ph, TermList(0,false));
  // if (_formulaIndex.isVacuous(tr.transform(ctx._cls.begin()->second[0]))) {
  //   env.statistics->vacuousInductionFormulaDiscardedDynamically2++;
  //   _formulaIndex.makeVacuous(ctx, e);
  //   return false;
  // }
  if (isVacuous(lit, ph)) {
    e->_vacuous = true;
    env.statistics->vacuousInductionFormulaDiscardedStatically++;
    return true;
  }

  return false;
}

}

}
