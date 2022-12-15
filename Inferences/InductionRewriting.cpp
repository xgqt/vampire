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
 * @file InductionRewriting.cpp
 * Implements class InductionRewriting.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "InductionHelper.hpp"

#include "InductionRewriting.hpp"

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

void InductionRewriting::attach(SaturationAlgorithm* salg)
{
  CALL("InductionRewriting::attach");
  GeneratingInferenceEngine::attach(salg);
  _lhsIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(_forward ? FORWARD_REWRITING_LHS_INDEX : BACKWARD_REWRITING_LHS_INDEX) );
  _termIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(_forward ? FORWARD_REWRITING_SUBTERM_INDEX : BACKWARD_REWRITING_SUBTERM_INDEX) );
}

void InductionRewriting::detach()
{
  CALL("InductionRewriting::detach");
  _termIndex = 0;
  _salg->getIndexManager()->release(_forward ? FORWARD_REWRITING_SUBTERM_INDEX : BACKWARD_REWRITING_SUBTERM_INDEX);
  _lhsIndex = 0;
  _salg->getIndexManager()->release(_forward ? FORWARD_REWRITING_LHS_INDEX : BACKWARD_REWRITING_LHS_INDEX);
  GeneratingInferenceEngine::detach();
}

ClauseIterator InductionRewriting::generateClauses(Clause* premise)
{
  CALL("InductionRewriting::generateClauses");
  auto& ord = _salg->getOrdering();

  // forward result
  auto fwRes = iterTraits(getIterator(ord, premise, _forward))
    .flatMap([](pair<Literal*,Term*> kv) {
      NonVariableNonTypeIterator it(kv.second, true);
      return pvi( pushPairIntoRightIterator(kv.first, getUniquePersistentIteratorFromPtr(&it)) );
    })
    .flatMap([this](pair<Literal*, TermList> arg) {
      return pvi( pushPairIntoRightIterator(arg, _lhsIndex->getUnifications(arg.second, true)) );
    })
    .flatMap([this, premise](pair<pair<Literal*, TermList>, TermQueryResult> arg) {
      TermQueryResult& qr = arg.second;
      return perform(premise, arg.first.first, arg.first.second,
        qr.clause, qr.literal, qr.term, qr.substitution, true);
    })
    .timeTraced(_forward ? "forward induction forward rewriting" : "forward induction backward rewriting");

  // backward result
  auto bwRes = iterTraits(getIterator(ord, premise, _forward))
    .filter([&ord,this](pair<Literal*,Term*> kv) {
      auto lit = kv.first;
      if (!lit->isEquality() || lit->isNegative()) {
        return false;
      }
      TermList lhs(kv.second);
      return InductionRewriting::areEqualitySidesOriented(lhs, EqHelper::getOtherEqualitySide(lit, lhs), ord, _forward);
    })
    .flatMap([this](pair<Literal*, Term*> kv) {
      return pvi( pushPairIntoRightIterator(make_pair(kv.first, TermList(kv.second)), _termIndex->getUnifications(TermList(kv.second), true)) );
    })
    .flatMap([this, premise](pair<pair<Literal*, TermList>, TermQueryResult> arg) {
      TermQueryResult& qr = arg.second;
      return perform(qr.clause, qr.literal, qr.term,
        premise, arg.first.first, arg.first.second, qr.substitution, false);
    })
    .timeTraced(_forward ? "backward induction forward rewriting" : "backward induction backward rewriting");

  return pvi(fwRes.concat(bwRes)
    .filter(NonzeroFn())
    .timeTraced(_forward ? "induction forward rewriting" : "induction backward rewriting"));
}

Term* getRewrittenTerm(Literal* oldLit, Literal* newLit) {
  // cout << *oldLit << " " << *newLit << endl;
  ASS_EQ(oldLit->functor(), newLit->functor());
  ASS_NEQ(newLit,oldLit);
  if (oldLit->commutative()) {
    auto lhsNew = *newLit->nthArgument(0);
    auto rhsNew = *newLit->nthArgument(1);
    auto lhsOld = *oldLit->nthArgument(0);
    auto rhsOld = *oldLit->nthArgument(1);
    if (lhsNew == lhsOld || rhsNew == lhsOld) {
      ASS(rhsOld.isTerm());
      return rhsOld.term();
    }
    ASS(lhsOld.isTerm());
    ASS(lhsNew == rhsOld || rhsNew == rhsOld);
    return lhsOld.term();
  } else {
    for (unsigned i = 0; i < oldLit->arity(); i++) {
      auto oldArg = *oldLit->nthArgument(i);
      auto newArg = *newLit->nthArgument(i);
      if (oldArg != newArg) {
        ASS(oldArg.isTerm());
        return oldArg.term();
      }
    }
    ASSERTION_VIOLATION;
  }
}

// bool greaterSideRewritten(Literal* lit, Literal* orig, Ordering& ord) {
//   auto rwSide = getSideRewritten(lit, orig);
//   return ord.compare(rwSide, EqHelper::getOtherEqualitySide(orig, rwSide)) == Ordering::GREATER;
// }

void InductionRewriting::output()
{
  CALL("InductionRewriting::output");
  auto s = iterTraits(_eqs.items()).collect<Stack>();
  std::sort(s.begin(),s.end(),[](pair<Clause*,unsigned> kv1, pair<Clause*,unsigned> kv2) {
    return kv1.second < kv2.second;
  });
  cout << (_forward ? "forward" : "backward") << " eqs" << endl;
  for (const auto& kv : s) {
    cout << *kv.first << " " << kv.second << endl;
  }
  cout << "end " << endl << endl;
}

bool isTermViolatingBound(Term* bound, Term* t, Ordering& ord, bool forward)
{
  CALL("isTermViolatingBound");
  if (!bound) {
    return false;
  }
  auto comp = ord.compare(TermList(bound), TermList(t));
  if (forward) {
    if (comp == Ordering::Result::GREATER || comp == Ordering::Result::GREATER_EQ) {
      return true;
    }
  } else {
    if (comp == Ordering::Result::LESS || comp == Ordering::Result::LESS_EQ) {
      return true;
    }
  }
  return false;
}

VirtualIterator<pair<Literal*,Term*>> InductionRewriting::getIterator(Ordering& ord, Clause* premise, bool forward)
{
  CALL("InductionRewriting::getIterator");
  Term* bound;
  if (forward) {
    bound = premise->getRewritingUpperBound();
  } else {
    bound = premise->getRewritingLowerBound();
  }
  return pvi(iterTraits(premise->iterLits())
    .flatMap([](Literal* lit) {
      return pvi(pushPairIntoRightIterator(lit, termArgIter(lit)));
    })
    // filter out variables
    .map([](pair<Literal*, TermList> kv) { return make_pair(kv.first, kv.second.isTerm() ? kv.second.term() : nullptr); })
    .filter([](pair<Literal*, Term*> kv) { return kv.second!=nullptr; })
    // filter out ones violating the bound
    .filter([bound,&ord,forward](pair<Literal*, Term*> kv) {
      return !isTermViolatingBound(bound, kv.second, ord, forward);
    }));
}

bool InductionRewriting::areEqualitySidesOriented(TermList lhs, TermList rhs, Ordering& ord, bool forward)
{
  CALL("InductionRewriting::areTermsOriented");

  auto comp = ord.compare(rhs,lhs);
  if (forward && Ordering::isGorGEorE(comp)) {
    return false;
  }
  if (!forward && !Ordering::isGorGEorE(comp)) {
    return false;
  }
  return true;
}

ClauseIterator InductionRewriting::perform(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult)
{
  CALL("InductionRewriting::perform");
  // we want the rwClause and eqClause to be active
  ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);

  // cout << "performRemodulation with " << *rwClause << " and " << *eqClause << endl
  //   << "rwLit " << *rwLit << " eqLit " << *eqLit << endl
  //   << "rwTerm " << rwTerm << " eqLHS " << eqLHS << endl
  //   // << "subst " << endl << subst->tryGetRobSubstitution()->toString() << endl
  //   << "eqIsResult " << eqIsResult << endl << endl;

  if (eqLHS.isVar() || rwTerm.isVar()) {
    return ClauseIterator::getEmpty();
  }
  ASS(eqLHS.isTerm());

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  TermList tgtTermS = subst->applyTo(tgtTerm, eqIsResult);
  TermList rwTermS = subst->applyTo(rwTerm, !eqIsResult);
  Literal* rwLitS = subst->applyTo(rwLit, !eqIsResult);
  if (tgtTermS.isVar()) {
    return ClauseIterator::getEmpty();
  }

  if (!areEqualitySidesOriented(rwTermS, tgtTermS, _salg->getOrdering(), _forward)) {
    return ClauseIterator::getEmpty();
  }

  if (filterByHeuristics(rwClause, rwLit, rwTerm, eqClause, eqLit, eqLHS, subst)) {
    // static unsigned skippedByHeuristics = 0;
    // skippedByHeuristics++;
    // if (skippedByHeuristics % 1000 == 0) {
    //   cout << "skipped by heuristics " << skippedByHeuristics << endl;
    // }
    return ClauseIterator::getEmpty();
  }

  auto bound = _forward ? rwClause->getRewritingUpperBound() : rwClause->getRewritingLowerBound();
  Term* boundS = nullptr;
  if (bound) {
    // cout << "bound " << *bound << endl;
    boundS = subst->applyTo(TermList(bound), !eqIsResult).term();
    // cout << "bound after " << *boundS << endl;
  }

  return pvi(iterTraits(vi(new SingleOccurrenceReplacementIterator(rwLitS, rwTermS.term(), tgtTermS)))
    .map([this,eqClause,rwClause,eqLit,rwLit,rwLitS,eqIsResult,subst,boundS](Literal* tgtLitS) -> Clause* {
      if (EqHelper::isEqTautology(tgtLitS)) {
        return nullptr;
      }
      // if (!InductionHelper::isInductionLiteral(rwLit)) {
      //   return nullptr;
      // }
      auto rwArg = getRewrittenTerm(tgtLitS, rwLitS);
      // cout << "rwArg " << *rwArg << endl;
      if (isTermViolatingBound(boundS, rwArg, _salg->getOrdering(), _forward)) {
        // static unsigned skipped = 0;
        // skipped++;
        // if (skipped % 100 == 0) {
        //   cout << "skipped " << skipped << endl;
        // }
        return nullptr;
      }

      unsigned rwLength = rwClause->length();
      unsigned eqLength = eqClause->length();
      unsigned newLength = rwLength + (eqLength - 1);
      Inference inf(GeneratingInference2(
        _forward ? InferenceRule::INDUCTION_FORWARD_REWRITING : InferenceRule::INDUCTION_REMODULATION,
        rwClause, eqClause));
      Clause* newCl = new(newLength) Clause(newLength, inf);

      (*newCl)[0] = tgtLitS;
      int next = 1;
      for(unsigned i=0;i<rwLength;i++) {
        Literal* curr=(*rwClause)[i];
        if(curr!=rwLit) {
          // cout << "rwClause " << *curr << endl;
          Literal *currAfter = subst->applyTo(curr,!eqIsResult);
          // cout << "rwClause after " << *currAfter << endl;
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
          // cout << "eqClause " << *curr << endl;
          Literal *currAfter = subst->applyTo(curr,eqIsResult);
          // cout << "eqClause after " << *currAfter << endl;

          if (EqHelper::isEqTautology(currAfter)) {
            newCl->destroy();
            return nullptr;
          }

          (*newCl)[next++] = currAfter;
        }
      }
      ASS_EQ(next, newLength);

      if (_forward) {
        if (eqIsResult) {
          env.statistics->forwardInductionForwardRewriting++;
        } else {
          env.statistics->backwardInductionForwardRewriting++;
        }
      } else {
        if (eqIsResult) {
          env.statistics->forwardInductionBackwardRewriting++;
        } else {
          env.statistics->backwardInductionBackwardRewriting++;
        }
      }
      auto ptr = _eqs.findPtr(eqClause);
      if (!ptr) {
        _eqs.insert(eqClause, 1);
      } else {
        (*ptr)++;
      }
      // cout << "result " << *newCl << endl << endl;
      newCl->setRewritingBound(rwArg, !_forward);
      return newCl;
    }));
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

bool InductionRewriting::filterByHeuristics(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst)
{
  if (!termHasAllVarsOfClause(eqLHS, eqClause)) {
    return true;
  }

  vset<unsigned> eqSkolems = getSkolems(eqLit);
  if (!eqSkolems.empty()) {
    vset<unsigned> rwSkolems = getSkolems(rwLit);
    vset<unsigned> is;
    set_intersection(eqSkolems.begin(), eqSkolems.end(), rwSkolems.begin(), rwSkolems.end(), inserter(is, is.end()));
    if (is != eqSkolems) {
      return true;
    }
  }

  return false;
}

SimplifyingGeneratingInference::ClauseGenerationResult InductionSGIWrapper::generateSimplify(Clause* premise)
{
  CALL("InductionSGIWrapper::generateSimplify");
  // static unsigned cnt = 0;
  // cnt++;
  // if (cnt % 1000 == 0) {
  //   _fwRewriting->output();
  //   _bwRewriting->output();
  // }
  if (!premise->getRewritingLowerBound() && !premise->getRewritingUpperBound()) {
    return _generator->generateSimplify(premise);
  }
  ASS(!premise->getRewritingLowerBound() || !premise->getRewritingUpperBound());
  auto it = ClauseIterator::getEmpty();
  if (premise->getRewritingUpperBound()) {
    it = pvi(getConcatenatedIterator(it, _fwRewriting->generateClauses(premise)));
  }
  return ClauseGenerationResult {
    .clauses = pvi(iterTraits(it).concat(
      _induction->generateClauses(premise),
      _bwRewriting->generateClauses(premise))),
    .premiseRedundant = false,
  };
}

}
