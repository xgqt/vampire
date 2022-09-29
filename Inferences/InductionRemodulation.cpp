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
 * @file InductionRemodulation.cpp
 * Implements class InductionRemodulation.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "InductionHelper.hpp"

#include "InductionRemodulation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

TermList SingleOccurrenceReplacementIterator::Replacer::transformSubterm(TermList trm)
{
  CALL("SingleOccurrenceReplacementIterator::Replacer::transformSubterm");

  if (trm.isVar() || _matchCount > _i) {
    return trm;
  }
  if (trm.term() == _o && _i == _matchCount++) {
    return _r;
  }
  return trm;
}

Literal* SingleOccurrenceReplacementIterator::next()
{
  CALL("SingleOccurrenceReplacementIterator::next");
  ASS(hasNext());
  Replacer sor(_o, _r, _iteration++);
  return sor.transform(_lit);
}

void InductionRemodulation::attach(SaturationAlgorithm* salg)
{
  CALL("InductionRemodulation::attach");
  GeneratingInferenceEngine::attach(salg);
  _lhsIndex=static_cast<RemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(REMODULATION_LHS_SUBST_TREE) );
  _termIndex=static_cast<RemodulationSubtermIndex*>(
	  _salg->getIndexManager()->request(REMODULATION_SUBTERM_INDEX) );
}

void InductionRemodulation::detach()
{
  CALL("InductionRemodulation::detach");
  _lhsIndex = 0;
  _salg->getIndexManager()->release(REMODULATION_LHS_SUBST_TREE);
  _termIndex = 0;
  _salg->getIndexManager()->release(REMODULATION_SUBTERM_INDEX);
  GeneratingInferenceEngine::detach();
}

struct ReverseLHSIteratorFn {
  ReverseLHSIteratorFn(Clause* cl) : _cl(cl) {}
  VirtualIterator<pair<Literal*, TermList>> operator()(pair<Literal*, TermList> arg)
  {
    CALL("ReverseLHSIteratorFn()");
    auto rhs = EqHelper::getOtherEqualitySide(arg.first, arg.second);
    if (!canUseForRewrite(arg.first, _cl) ||
        !termHasAllVarsOfClause(rhs, _cl)) {
      return VirtualIterator<pair<Literal*, TermList>>::getEmpty();
    }
    if (env.options->inductionRemodulationRedundancyCheck() && !hasTermToInductOn(arg.second.term(), arg.first)) {
      return VirtualIterator<pair<Literal*, TermList>>::getEmpty();
    }
    return pvi(getSingletonIterator(make_pair(arg.first,rhs)));
  }
private:
  Clause* _cl;
};

ClauseIterator InductionRemodulation::generateClauses(Clause* premise)
{
  CALL("InductionRemodulation::generateClauses");
  ClauseIterator res1 = ClauseIterator::getEmpty();

  if (InductionHelper::isInductionClause(premise))
  {
    // forward result
    res1 = pvi(iterTraits(premise->iterLits())
      .filter(&InductionHelper::isInductionLiteral)
      .flatMap([](Literal* lit) {
        NonVariableNonTypeIterator it(lit);
        return pvi( pushPairIntoRightIterator(lit, getUniquePersistentIteratorFromPtr(&it)) );
      })
      .flatMap([this](pair<Literal*, TermList> arg) {
        return pvi( pushPairIntoRightIterator(arg, _lhsIndex->getUnifications(arg.second, true)) );
      })
      .flatMap([this, premise](pair<pair<Literal*, TermList>, TermQueryResult> arg) {
        TermQueryResult& qr = arg.second;
        return perform(premise, arg.first.first, arg.first.second,
          qr.clause, qr.literal, qr.term, qr.substitution, true);
      }));
  }

  // backward result
  ClauseIterator res2 = ClauseIterator::getEmpty();
  if (canUseForRewrite(premise)) {
    res2 = pvi(iterTraits(premise->iterLits())
      .flatMap(EqHelper::LHSIteratorFn(_salg->getOrdering()))
      .flatMap(ReverseLHSIteratorFn(premise))
      .flatMap([this](pair<Literal*, TermList> arg) {
        return pvi( pushPairIntoRightIterator(arg, _termIndex->getUnifications(arg.second, true)) );
      })
      .flatMap([this, premise](pair<pair<Literal*, TermList>, TermQueryResult> arg) {
        TermQueryResult& qr = arg.second;
        return perform(qr.clause, qr.literal, qr.term,
          premise, arg.first.first, arg.first.second, qr.substitution, false);
      }));
  }

  return pvi(iterTraits(getConcatenatedIterator(res1,res2))
    .filter(NonzeroFn())
    .timeTraced("induction remodulation"));
}

vset<unsigned> getSkolems(Literal* lit) {
  vset<unsigned> res;
  NonVariableNonTypeIterator it(lit);
  while (it.hasNext()) {
    auto trm = it.next();
    if (env.signature->getFunction(trm.term()->functor())->skolem()) {
      res.insert(trm.term()->functor());
    }
  }
  return res;
}

ClauseIterator InductionRemodulation::perform(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult)
{
  CALL("InductionRemodulation::perform");
  // we want the rwClause and eqClause to be active
  ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);

  vset<unsigned> eqSkolems = getSkolems(eqLit);
  if (!eqSkolems.empty()) {
    vset<unsigned> rwSkolems = getSkolems(rwLit);
    vset<unsigned> is;
    set_intersection(eqSkolems.begin(), eqSkolems.end(), rwSkolems.begin(), rwSkolems.end(), inserter(is, is.end()));
    if (is != eqSkolems) {
      return ClauseIterator::getEmpty();
    }
  }

  // cout << "performRemodulation with " << *rwClause << " and " << *eqClause << endl
  //   << "rwLit " << *rwLit << " eqLit " << *eqLit << endl
  //   << "rwTerm " << rwTerm << " eqLHS " << eqLHS << endl
  //   // << "subst " << endl << subst->tryGetRobSubstitution()->toString() << endl
  //   << "eqIsResult " << eqIsResult << endl;

  if (eqLHS.isVar()) {
    TermList eqLHSsort = SortHelper::getEqualityArgumentSort(eqLit);
    TermList tgtTermSort = SortHelper::getTermSort(rwTerm, rwLit);
    if (eqLHSsort != tgtTermSort) {
      return ClauseIterator::getEmpty();
    }
  }

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  TermList tgtTermS = subst->apply(tgtTerm,eqIsResult);
  Literal* rwLitS = subst->apply(rwLit,!eqIsResult);
  TermList rwTermS = subst->apply(rwTerm,!eqIsResult);

  auto comp = _salg->getOrdering().compare(tgtTermS,rwTermS);
  if (comp != Ordering::GREATER && comp != Ordering::GREATER_EQ) {
    ASS_NEQ(comp, Ordering::INCOMPARABLE);
    return ClauseIterator::getEmpty();
  }

  return pvi(iterTraits(vi(new SingleOccurrenceReplacementIterator(rwLitS, rwTermS.term(), TermList(tgtTermS.term()))))
    .map([eqClause,rwClause,eqLit,rwLit,eqIsResult,subst](Literal* tgtLitS) -> Clause* {
      if(EqHelper::isEqTautology(tgtLitS)) {
        return nullptr;
      }

      unsigned rwLength = rwClause->length();
      unsigned eqLength = eqClause->length();
      unsigned newLength = rwLength + (eqLength - 1);
      Inference inf(GeneratingInference2(InferenceRule::INDUCTION_REMODULATION, rwClause, eqClause));
      Clause* newCl = new(newLength) Clause(newLength, inf);

      (*newCl)[0] = tgtLitS;
      int next = 1;
      for(unsigned i=0;i<rwLength;i++) {
        Literal* curr=(*rwClause)[i];
        if(curr!=rwLit) {
          Literal *currAfter = subst->apply(curr,!eqIsResult);

          if (EqHelper::isEqTautology(currAfter)) {
            newCl->destroy();
            return nullptr;
          }

          (*newCl)[next++] = currAfter;
        }
      }

      for (unsigned i = 0; i < eqLength; i++) {
        Literal *curr = (*eqClause)[i];
        if (curr != eqLit) {
          Literal *currAfter = subst->apply(curr,eqIsResult);

          if (EqHelper::isEqTautology(currAfter)) {
            newCl->destroy();
            return nullptr;
          }

          (*newCl)[next++] = currAfter;
        }
      }
      ASS_EQ(next, newLength);

      env.statistics->inductionRemodulation++;
      // cout << "result " << *newCl << endl << endl;
      newCl->markInductionClause();
      return newCl;
    }));
}

}
