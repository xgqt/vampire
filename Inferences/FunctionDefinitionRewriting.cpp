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
 * @file FunctionDefinitionRewriting.cpp
 * Implements class FunctionDefinitionRewriting.
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

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/FunctionDefinitionIndex.hpp"
#include "Shell/Options.hpp"

#include "FunctionDefinitionRewriting.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Saturation;

ClauseIterator FunctionDefinitionRewriting::generateClauses(Clause *premise)
{
  CALL("FunctionDefinitionRewriting::generateClauses");

  auto it = iterTraits(premise->iterLits())
    .flatMap([](Literal *lit) {
      NonVariableIterator nvi(lit);
      return pvi(pushPairIntoRightIterator(lit,
          getUniquePersistentIteratorFromPtr(&nvi)));
    })
    .flatMap([](pair<Literal *, TermList> arg) {
      return pvi(pushPairIntoRightIterator(arg, FunctionDefinitionIndex::getGeneralizations(arg.second)));
    })
    .map([premise](pair<pair<Literal *, TermList>, TermQueryResult> arg) {
      TermQueryResult &tqr = arg.second;
      bool temp;
      return FunctionDefinitionRewriting::perform(premise, arg.first.first, arg.first.second, tqr, false, temp,
        Inference(GeneratingInference2(InferenceRule::FUNCTION_DEFINITION_REWRITING, premise, tqr.clause)));
    });

  return getTimeCountedIterator(getFilteredIterator(it, NonzeroFn()), TC_FUNCTION_DEFINITION_REWRITING);
}

bool FunctionDefinitionRewriting::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("FunctionDefinitionRewriting::perform/1");

  TimeCounter tc(TC_FUNCTION_DEFINITION_DEMODULATION);

  Ordering& ordering = ForwardSimplificationEngine::_salg->getOrdering();

  static DHSet<TermList> attempted;
  attempted.reset();

  unsigned cLen = cl->length();
  for (unsigned li = 0; li < cLen; li++) {
    Literal* lit = (*cl)[li];
    NonVariableIterator it(lit);
    while (it.hasNext()) {
      TermList trm = it.next();
      if (!attempted.insert(trm)) {
        it.right();
        continue;
      }

      bool toplevelCheck = ForwardSimplificationEngine::_salg->getOptions().demodulationRedundancyCheck() &&
        lit->isEquality() && (trm==*lit->nthArgument(0) || trm==*lit->nthArgument(1));

      auto git = FunctionDefinitionIndex::getGeneralizations(trm);
      while (git.hasNext()) {
        TermQueryResult tqr = git.next();
        if (tqr.clause->length() != 1) {
          continue;
        }
        auto rhs = EqHelper::getOtherEqualitySide(tqr.literal, tqr.term);
        if (Ordering::isGorGEorE(ordering.compare(rhs,tqr.term))) {
          continue;
        }
        bool isEqTautology = false;
        auto res = FunctionDefinitionRewriting::perform(cl, lit, trm, tqr, toplevelCheck, isEqTautology,
          Inference(SimplifyingInference2(InferenceRule::FUNCTION_DEFINITION_DEMODULATION, cl, tqr.clause)), ForwardSimplificationEngine::_salg);
        if (!res && !isEqTautology) {
          continue;
        }
        if (!isEqTautology) {
          replacement = res;
        }
        premises = pvi(getSingletonIterator(tqr.clause));
        return true;
      }
    }
  }

  return false;
}

Clause *FunctionDefinitionRewriting::perform(
    Clause *rwClause, Literal *rwLit, TermList rwTerm,
    const TermQueryResult& tqr, bool toplevelCheck, bool& isEqTautology,
    const Inference& inf, SaturationAlgorithm* salg)
{
  CALL("FunctionDefinitionRewriting::perform/2");

  if (SortHelper::getTermSort(rwTerm, rwLit) != SortHelper::getEqualityArgumentSort(tqr.literal)) {
    // sorts don't match
    return 0;
  }

  ASS(!tqr.term.isVar());

  TermList tgtTerm = EqHelper::getOtherEqualitySide(tqr.literal, tqr.term);

  TermList tgtTermS;
  if (!tqr.substitution->isIdentityOnQueryWhenResultBound()) {
    //When we apply substitution to the rhs, we get a term, that is
    //a variant of the term we'd like to get, as new variables are
    //produced in the substitution application.
    TermList lhsSBadVars = tqr.substitution->applyToResult(tqr.term);
    TermList rhsSBadVars = tqr.substitution->applyToResult(tgtTerm);
    Renaming rNorm, qNorm, qDenorm;
    rNorm.normalizeVariables(lhsSBadVars);
    qNorm.normalizeVariables(tgtTerm);
    qDenorm.makeInverse(qNorm);
    ASS_EQ(rwTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
    tgtTermS = qDenorm.apply(rNorm.apply(rhsSBadVars));
  }
  else {
    tgtTermS = tqr.substitution->applyToBoundResult(tgtTerm);
  }

  if (toplevelCheck && !EqHelper::demodulationIsRedundant(rwClause, rwLit, rwTerm, tgtTermS, salg->getOrdering())) {
    return 0;
  }

  Literal *tgtLitS = EqHelper::replace(rwLit, rwTerm, tgtTermS);
  if (EqHelper::isEqTautology(tgtLitS)) {
    isEqTautology = true;
    return 0;
  }

  unsigned rwLength = rwClause->length();
  unsigned eqLength = tqr.clause->length();
  unsigned newLength = rwLength + eqLength - 1;

  Clause *res = new (newLength) Clause(newLength, inf);

  static bool doSimS = env.options->simulatenousSuperposition();
  (*res)[0] = tgtLitS;

  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr != rwLit) {
      if (doSimS) {
        curr = EqHelper::replace(curr, rwTerm, tgtTermS);
      }

      if (EqHelper::isEqTautology(curr)) {
        isEqTautology = true;
        res->destroy();
        return 0;
      }

      (*res)[next++] = curr;
    }
  }

  {
    for (unsigned i = 0; i < eqLength; i++) {
      Literal *curr = (*tqr.clause)[i];
      if (curr != tqr.literal) {
        Literal *currAfter;
        if (!tqr.substitution->isIdentityOnQueryWhenResultBound()) {
          // same as above for RHS
          TermList lhsSBadVars = tqr.substitution->applyToResult(tqr.term);
          Literal *currSBadVars = tqr.substitution->applyToResult(curr);
          Renaming rNorm, qNorm, qDenorm;
          rNorm.normalizeVariables(lhsSBadVars);
          qNorm.normalizeVariables(curr);
          qDenorm.makeInverse(qNorm);
          ASS_EQ(rwTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
          currAfter = qDenorm.apply(rNorm.apply(currSBadVars));
        }
        else {
          currAfter = tqr.substitution->applyToBoundResult(curr);
        }

        if (EqHelper::isEqTautology(currAfter)) {
          isEqTautology = true;
          res->destroy();
          return 0;
        }

        (*res)[next++] = currAfter;
      }
    }
  }

  return res;
}
