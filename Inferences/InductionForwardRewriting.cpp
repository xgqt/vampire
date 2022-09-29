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
 * @file InductionForwardRewriting.cpp
 * Implements class InductionForwardRewriting.
 */

#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Indexing/IndexManager.hpp"

#include "Shell/Options.hpp"

#include "InductionForwardRewriting.hpp"
#include "InductionHelper.hpp"
#include "InductionRemodulation.hpp"

ClauseIterator InductionForwardRewriting::generateClauses(Clause *premise)
{
  CALL("InductionForwardRewriting::generateClauses");

  ClauseIterator res = ClauseIterator::getEmpty();
  if (InductionHelper::isInductionClause(premise) || canUseForRewrite(premise)) {
    res = pvi(iterTraits(premise->iterLits())
      .filter([premise](Literal* lit){
        return canUseForRewrite(lit, premise) || InductionHelper::isInductionLiteral(lit);
      })
      .flatMap([](Literal* lit){
        return pvi(pushPairIntoRightIterator(lit, getUniquePersistentIterator(vi(new NonVariableIterator(lit)))));
      })
      // Get clauses with a function definition literal whose lhs is a generalization of the rewritable subterm,
      // returns a pair with the original pair and the generalization result (includes substitution)
      .flatMap([this](pair<Literal *, TermList> arg) {
        return pvi(pushPairIntoRightIterator(arg, _index->getUnifications(arg.second)));
      })
      //Perform forward rewriting
      .map([this, premise](pair<pair<Literal *, TermList>, TermQueryResult> arg) {
        TermQueryResult &qr = arg.second;
        return perform(
          premise, arg.first.first, arg.first.second, qr.clause,
          qr.literal, qr.term, qr.substitution, true);
      }));
  }
  if (canUseForRewrite(premise))
  {
    auto it = pvi(iterTraits(premise->iterLits())
      .flatMap([this](Literal* lit) {
        return pvi(pushPairIntoRightIterator(lit, EqHelper::getLHSIterator(lit, _salg->getOrdering())));
      })
      .filter([premise](pair<Literal*, TermList> arg) {
        return termHasAllVarsOfClause(arg.second, premise);
      })
      .flatMap([this](pair<Literal*, TermList> arg) {
        return pvi(pushPairIntoRightIterator(arg, _tindex->getUnifications(arg.second, true)));
      })
      .map([this,premise](pair<pair<Literal*, TermList>, TermQueryResult> arg) {
        TermQueryResult& qr = arg.second;
        return perform(
          qr.clause, qr.literal, qr.term, premise, arg.first.first,
          arg.first.second, qr.substitution, false);
      }));

    res = pvi(getConcatenatedIterator(res, it));
  }
  // Remove null elements
  return pvi(iterTraits(res)
    .filter(NonzeroFn())
    .timeTraced("induction rewriting"));
}

Clause *InductionForwardRewriting::perform(
    Clause *rwClause, Literal *rwLit, TermList rwTerm,
    Clause *eqClause, Literal *eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult)
{
  CALL("InductionForwardRewriting::perform");
  // we want the rwClause and eqClause to be active
  ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);

  //TODO: do we need rewriting from variables?

  if (SortHelper::getTermSort(rwTerm, rwLit) != SortHelper::getEqualityArgumentSort(eqLit)) {
    // sorts don't match
    return 0;
  }

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  // TermList tgtTermS = eqIsResult ? subst->applyToBoundResult(tgtTerm) : subst->applyToBoundQuery(tgtTerm);
  TermList tgtTermS = subst->apply(tgtTerm, eqIsResult);
  Literal* rwLitS = subst->apply(rwLit, !eqIsResult);
  TermList rwTermS = subst->apply(rwTerm, !eqIsResult);

  Ordering& ordering = _salg->getOrdering();
  if(Ordering::isGorGEorE(ordering.compare(tgtTermS,rwTermS))) {
    ASS_NEQ(ordering.compare(tgtTermS,rwTermS), Ordering::INCOMPARABLE);
    return 0;
  }

  // This inference is covered by superposition if:
  // 1. eqLit is selected in eqClause and
  // 2. rwTerm is a rewritable subterm of a selected literals of rwClause
  //    (or of rwLit if simultaneous superposition is off)
  static bool doSimS = _salg->getOptions().simulatenousSuperposition();
  bool selected = false;
  for (unsigned i = 0; i < eqClause->numSelected(); i++) {
    if ((*eqClause)[i] == eqLit) {
      selected = true;
      break;
    }
  }
  if (selected) {
    if (doSimS) {
      for (unsigned i = 0; i < rwClause->numSelected(); i++) {
        auto rwstit = EqHelper::getSubtermIterator((*rwClause)[i], ordering);
        while (rwstit.hasNext()) {
          if (rwTerm == rwstit.next()) {
            return 0;
          }
        }
      }
    } else {
      auto rwstit = EqHelper::getSubtermIterator(rwLit, ordering);
      while (rwstit.hasNext()) {
        if (rwTerm == rwstit.next()) {
          return 0;
        }
      }
    }
  }

  // Literal *tgtLitS = EqHelper::replace(rwLit, rwTerm, tgtTermS);
  Literal* tgtLitS = EqHelper::replace(rwLitS,rwTermS,tgtTermS);
  if (EqHelper::isEqTautology(tgtLitS)) {
    return 0;
  }

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  unsigned newLength = rwLength + eqLength - 1;

  Inference inf(GeneratingInference2(InferenceRule::INDUCTION_FORWARD_REWRITING, rwClause, eqClause));
  Clause *res = new (newLength) Clause(newLength, inf);

  (*res)[0] = tgtLitS;
  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr != rwLit) {
      Literal* currAfter = subst->apply(curr, !eqIsResult);
      // curr = EqHelper::replace(curr, rwTerm, tgtTermS);

      if (doSimS) {
        currAfter = EqHelper::replace(currAfter,rwTermS,tgtTermS);
      }

      if(EqHelper::isEqTautology(currAfter)) {
        res->destroy();
        return 0;
      }

      (*res)[next++] = currAfter;
    }
  }

  {
    for (unsigned i = 0; i < eqLength; i++) {
      Literal *curr = (*eqClause)[i];
      if (curr != eqLit) {
        Literal* currAfter = subst->apply(curr, eqIsResult);
        // Literal *currAfter = eqIsResult ? subst->applyToBoundResult(curr) : subst->applyToBoundQuery(curr);

        if (EqHelper::isEqTautology(currAfter)) {
          res->destroy();
          return 0;
        }

        (*res)[next++] = currAfter;
      }
    }
  }
  env.statistics->inductionForwardRewriting++;
  return res;
}
