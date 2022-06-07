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
 * @file InductionHypothesisRewriting.cpp
 * Implements class InductionHypothesisRewriting.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/Splitter.hpp"

#include "InductionHypothesisRewriting.hpp"
#include "InductionHelper.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;

struct FilterFn
{
  bool operator()(const pair<TermQueryResult, TermQueryResult>& p) const {
    vset<unsigned> mainSk = InductionHelper::collectInductionSkolems(p.first.literal, p.first.clause);
    if (mainSk.empty()) {
      return false;
    }
    vset<unsigned> sideSk = InductionHelper::collectInductionSkolems(p.second.literal, p.second.clause);
    if (sideSk.empty()) {
      return false;
    }
    return includes(mainSk.begin(), mainSk.end(), sideSk.begin(), sideSk.end());
  }
};

ClauseIterator InductionHypothesisRewriting::generateClauses(Clause *premise)
{
  CALL("InductionHypothesisRewriting::generateClauses(Clause*)");

  return pvi( iterTraits(premise->iterLits())
    .filter([premise](Literal* lit) {
      return lit->isEquality() && InductionHelper::isInductionLiteral(lit, premise);
    })
    .flatMap([](Literal* lit) {
      TermIterator it;
      if (lit->isNegative()) {
        NonVariableNonTypeIterator nvi(lit);
        it = pvi(getUniquePersistentIteratorFromPtr(&nvi));
      } else {
        it = EqHelper::getEqualityArgumentIterator(lit);
      }
      return pvi( pushPairIntoRightIterator(lit, it) );
    })
    .flatMap([this,premise](const pair<Literal*, TermList>& kv) {
      TermQueryResult qr(kv.second, kv.first, premise);
      if (kv.first->isNegative()) {
        return pvi( pushPairIntoRightIterator(qr, _lhsIndex->getGeneralizations(qr.term)) );
      } else {
        return pvi( getMappingIterator(_stIndex->getInstances(qr.term), PairLeftPushingFn<TermQueryResult, TermQueryResult>(qr)) );
      }
    })
    .filter(FilterFn())
    .flatMap([](const pair<TermQueryResult, TermQueryResult>& p) {
      return pvi( pushPairIntoRightIterator(p, EqHelper::getEqualityArgumentIterator(p.first.literal)) );
    })
    .flatMap([this](const pair<pair<TermQueryResult, TermQueryResult>, TermList>& p) {
      auto& qr1 = p.first.first;
      auto& qr2 = p.first.second;

      vset<unsigned> sk = InductionHelper::collectInductionSkolems(qr2.literal, qr2.clause);
      return perform(sk, qr1.clause, qr1.literal, p.second, qr1.term,
        qr2.clause, qr2.literal, qr2.term,
        qr1.substitution ? qr1.substitution : qr2.substitution, !qr1.substitution);
    }));
}

ClauseIterator InductionHypothesisRewriting::perform(const vset<unsigned>& sig,
    Clause *rwClause, Literal *rwLit, TermList rwSide, TermList rwTerm,
    Clause *eqClause, Literal *eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult)
{
  CALL("InductionHypothesisRewriting::perform");

  if (SortHelper::getTermSort(rwTerm, rwLit) != SortHelper::getEqualityArgumentSort(eqLit)) {
    // sorts don't match
    return ClauseIterator::getEmpty();
  }

  if (!rwSide.containsSubterm(rwTerm)) {
    return ClauseIterator::getEmpty();
  }

  ASS(!eqLHS.isVar());

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  TermList tgtTermS;
  if ((eqIsResult && !subst->isIdentityOnQueryWhenResultBound()) || (!eqIsResult && !subst->isIdentityOnResultWhenQueryBound())) {
    //When we apply substitution to the rhs, we get a term, that is
    //a variant of the term we'd like to get, as new variables are
    //produced in the substitution application.
    TermList lhsSBadVars = subst->apply(eqLHS, eqIsResult);
    TermList rhsSBadVars = subst->apply(tgtTerm, eqIsResult);
    Renaming rNorm, qNorm, qDenorm;
    rNorm.normalizeVariables(lhsSBadVars);
    qNorm.normalizeVariables(tgtTerm);
    qDenorm.makeInverse(qNorm);
    ASS_EQ(rwTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
    tgtTermS = qDenorm.apply(rNorm.apply(rhsSBadVars));
  }
  else {
    tgtTermS = eqIsResult ? subst->applyToBoundResult(tgtTerm) : subst->applyToBoundQuery(tgtTerm);
  }

  TermList rwSideS(EqHelper::replace(rwSide.term(), rwTerm, tgtTermS));
  if (rwSide == rwTerm) {
    rwSideS = tgtTermS;
  }
  Stack<TermList> args;
  args.push(rwSideS);
  args.push(EqHelper::getOtherEqualitySide(rwLit, rwSide));
  Literal *tgtLitS = Literal::create(rwLit, args.begin());

  // cout << "HYP: " << *eqLit << endl
  //      << "SRC: " << eqLHS << endl
  //      << "TGT: " << tgtTerm << endl
  //      << "RWSIDE: " << rwSideS << endl
  //      << "TGTLIT: " << *tgtLitS << endl;

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  unsigned newLength = rwLength + eqLength - 1;

  Inference inf(GeneratingInference2(InferenceRule::IH_REWRITING, rwClause, eqClause));
  Clause *newCl = new (newLength) Clause(newLength, inf);

  (*newCl)[0] = tgtLitS;
  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr != rwLit) {
      if (EqHelper::isEqTautology(curr)) {
        newCl->destroy();
        return ClauseIterator::getEmpty();
      }

      (*newCl)[next++] = curr;
    }
  }

  {
    for (unsigned i = 0; i < eqLength; i++) {
      Literal *curr = (*eqClause)[i];
      if (curr != eqLit) {
        Literal *currAfter;
        if ((eqIsResult && !subst->isIdentityOnQueryWhenResultBound()) || (!eqIsResult && !subst->isIdentityOnResultWhenQueryBound())) {
          // same as above for RHS
          TermList lhsSBadVars = subst->apply(eqLHS, eqIsResult);
          Literal *currSBadVars = subst->apply(curr, eqIsResult);
          Renaming rNorm, qNorm, qDenorm;
          rNorm.normalizeVariables(lhsSBadVars);
          qNorm.normalizeVariables(curr);
          qDenorm.makeInverse(qNorm);
          ASS_EQ(rwTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
          currAfter = qDenorm.apply(rNorm.apply(currSBadVars));
        }
        else {
          currAfter = eqIsResult ? subst->applyToBoundResult(curr) : subst->applyToBoundQuery(curr);
        }

        if (EqHelper::isEqTautology(currAfter)) {
          newCl->destroy();
          return ClauseIterator::getEmpty();
        }

        (*newCl)[next++] = currAfter;
      }
    }
  }

  if (_splitter) {
    _splitter->onNewClause(newCl);
  }
  auto temp = _dupLitRemoval->simplify(newCl);
  if (temp != newCl) {
    if (_splitter) {
      _splitter->onNewClause(newCl);
    }
    newCl = temp;
  }
  for (const auto& fn : sig) {
    newCl->inference().removeFromInductionInfo(fn);
  }
  return pvi(getConcatenatedIterator(generateClauses(newCl), _induction->generateClauses(newCl)));
}
