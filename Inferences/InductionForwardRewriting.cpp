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

// based on Ordering::removeNonMaximal
void separateMaximals(Ordering& ord, List<pair<Literal*,Term*>>*& maximal, List<pair<Literal*,Term*>>*& rest)
{
  CALL("separateMaximals");

  List<pair<Literal*,Term*>>** ptr1 = &maximal;
  while (*ptr1) {
    List<pair<Literal*,Term*>>** ptr2 = &(*ptr1)->tailReference();
    while (*ptr2 && *ptr1) {
      Ordering::Result res = ord.compare(TermList((*ptr1)->head().second), TermList((*ptr2)->head().second));

      if (res == Ordering::GREATER || res == Ordering::GREATER_EQ
          || res == Ordering::EQUAL) {
        List<pair<Literal*,Term*>>::push(List<pair<Literal*,Term*>>::pop(*ptr2),rest);
        continue;
      } else if (res == Ordering::LESS || res == Ordering::LESS_EQ) {
        List<pair<Literal*,Term*>>::push(List<pair<Literal*,Term*>>::pop(*ptr1),rest);
        goto topLevelContinue;
      }/*  else {
        ASSERTION_VIOLATION;
      } */
      ptr2 = &(*ptr2)->tailReference();
    }
    ptr1 = &(*ptr1)->tailReference();
    topLevelContinue: ;
  }
}

VirtualIterator<pair<pair<Literal*,Term*>,TermList>> InductionForwardRewriting::getRewritingsIterator(Ordering& ord, Clause* premise)
{
  CALL("InductionForwardRewriting::getRewritingsIterator");
  TIME_TRACE("iterator creation");
  Term* lastRewritten = premise->getLastRewrittenTerm();
  auto res = VirtualIterator<pair<pair<Literal*,Term*>,TermList>>::getEmpty();

  // get all top-level terms
  DHSet<pair<Literal*,Term*>> terms;
  terms.loadFromIterator(iterTraits(premise->iterLits())
    // .filter([](Literal* lit) { return lit->ground(); })
    .flatMap([](Literal* lit) {
      return pvi(pushPairIntoRightIterator(lit, termArgIter(lit)));
    })
    .map([](pair<Literal*, TermList> kv) { return make_pair(kv.first, kv.second.isTerm() ? kv.second.term() : nullptr); })
    .filter([](pair<Literal*, Term*> kv) { return kv.second!=nullptr; }));
  if (terms.isEmpty()) {
    return res;
  }
  // // comparison iterator
  // auto cit = iterTraits(decltype(terms)::Iterator(terms))
  //   .flatMap([](pair<Literal*,Term*> kv) {
  //     // return pvi(pushPairIntoRightIterator(make_pair(kv.first,nullptr), pvi(iterTraits(getUniquePersistentIterator(vi(new NonVariableNonTypeIterator(kv.second, true)))))));
  //     return pvi(pushPairIntoRightIterator(kv, pvi(iterTraits(getUniquePersistentIterator(vi(new NonVariableNonTypeIterator(kv.second, true)))))));
  //   });
  // while (cit.hasNext()) {
  //   auto val = cit.next();
  //   res = pvi(getConcatenatedIterator(res, getSingletonIterator(val)));
  // }
  // return res;

  // filter out terms and their subterms that are greater or equal (?) than last rewritten
  auto termsL = List<pair<Literal*,Term*>>::empty();
  DHSet<TermList> done;
  List<pair<Literal*,Term*>>::pushFromIterator(iterTraits(decltype(terms)::Iterator(terms))
    .filter([lastRewritten,&ord,&done](pair<Literal*, Term*> kv) {
      if (lastRewritten) {
        auto comp = ord.compare(TermList(lastRewritten), TermList(kv.second));
        // term is greater than the last rewritten
        if (comp == Ordering::LESS || comp == Ordering::LESS_EQ) {
          done.loadFromIterator(NonVariableNonTypeIterator(kv.second,true));
          return false;
        }
      }
      return true;
    }), termsL);

  if (!lastRewritten) {
    auto rest = List<pair<Literal*,Term*>>::empty();
    separateMaximals(ord, termsL, rest);
    iterTraits(List<pair<Literal*,Term*>>::Iterator(termsL)).forEach([&done](pair<Literal*, Term*> kv){
      done.loadFromIterator(NonVariableNonTypeIterator(kv.second,true));
    });
    ASS(termsL);
    termsL = rest;
  }
  // if (lastRewritten) {
    // cout << "clause " << *premise << endl;
    // cout << "last rewritten is " << (lastRewritten ? lastRewritten->toString() : "none") << endl;
    // cout << "smaller than that are" << endl;
    // List<pair<Literal*,Term*>>::Iterator testit(termsL);
    // while(testit.hasNext()) {
    //   auto kv = testit.next();
    //   cout << "term " << *kv.second << " from " << *kv.first << endl;
    // }
    // cout << endl;
  // }

  static unsigned cnt = 0;
  cnt += done.size();
  // if (cnt % 1000 < 5) {
  //   cout << "rewriting skipped on " << cnt << " terms so far" << endl;
  // }

  // cout << "triples" << endl;
  while (termsL) {
    auto rest = List<pair<Literal*,Term*>>::empty();
    separateMaximals(ord, termsL, rest);
    auto it = iterTraits(List<pair<Literal*,Term*>>::Iterator(termsL))
        .flatMap([&done](pair<Literal*,Term*> kv) {
          return pvi(pushPairIntoRightIterator(kv, pvi(iterTraits(getUniquePersistentIterator(vi(new NonVariableNonTypeIterator(kv.second, true))))
            .filter([&done](TermList st) {
              return st.isTerm() && !done.contains(st);
            }))));
        });
    // TODO 'done' is deallocated if we don't evaluate the above iterator here
    while (it.hasNext()) {
      auto val = it.next();
      // cout << "literal " << *val.first.first << " rewritten " << *val.first.second << " term " << val.second << endl;
      res = pvi(getConcatenatedIterator(res, getSingletonIterator(val)));
      done.insert(val.second);
    }
    List<pair<Literal*,Term*>>::destroy(termsL);

    termsL = rest;
  }
  // cout << endl;
  return res;
}

void InductionForwardRewriting::output()
{
  CALL("InductionForwardRewriting::output");
  auto s = iterTraits(_eqs.items()).collect<Stack>();
  std::sort(s.begin(),s.end(),[](pair<pair<Clause*,TermList>,unsigned> kv1, pair<pair<Clause*,TermList>,unsigned> kv2) {
    return kv1.second < kv2.second;
  });
  cout << "INDUCTION FORWARD REWRITING eqs" << endl;
  for (const auto& kv : s) {
    cout << *kv.first.first << " " << kv.first.second << " " << kv.second << endl;
  }
  cout << "end " << endl << endl;
}

ClauseIterator InductionForwardRewriting::generateClauses(Clause *premise)
{
  CALL("InductionForwardRewriting::generateClauses");
  // Term* lastRewritten = premise->getLastRewrittenTerm();
  // if (!lastRewritten) {
  //   auto ll = LiteralList::empty();
  //   LiteralList::pushFromIterator(premise->iterLits(),ll);
  //   auto& ord = _salg->getOrdering();
  //   ord.removeNonMaximal(ll);
  // }

  ClauseIterator res = ClauseIterator::getEmpty();
  // auto lastRewrittenIsLiteral = lastRewritten && lastRewritten->isLiteral();
  // if (InductionHelper::isInductionClause(premise)) {
    // auto test1 = iterTraits(getRewritingsIterator(_salg->getOrdering(), premise))
    //   .flatMap([this](pair<pair<Literal*,Term*>, TermList> arg) {
    //     // cout << "literal " << *arg.first.first << " rewritten " << *arg.first.second << " term " << arg.second << endl;
    //     return pvi(pushPairIntoRightIterator(arg, _index->getUnifications(arg.second)));
    //   });
    // auto test2 = iterTraits(premise->iterLits())
    //   .flatMap([](Literal* lit){
    //     return pvi(pushPairIntoRightIterator(lit, termArgIter(lit)));
    //   })
    //   .map([](pair<Literal*, TermList> kv) { return make_pair(kv.first, kv.second.isTerm() ? kv.second.term() : nullptr); })
    //   .filter([](pair<Literal*, Term*> kv) { return kv.second!=nullptr; })
    //   .flatMap([](pair<Literal*, Term*> kv) {
    //     return pvi(pushPairIntoRightIterator(kv, getUniquePersistentIterator(vi(new NonVariableIterator(kv.second, true)))));
    //   })
    //   .flatMap([this](pair<pair<Literal *,Term*>, TermList> arg) {
    //     return pvi(pushPairIntoRightIterator(make_pair(arg, _index->getUnifications(arg.second))));
    //   });
    // auto test1cnt = 0;
    // while (test1.hasNext()) {
    //   test1cnt++;
    //   test1.next();
    // }
    // auto test2cnt = 0;
    // while (test2.hasNext()) {
    //   test2cnt++;
    //   test2.next();
    // }
    // if (test1cnt > test2cnt) {
    //   cout << test1cnt << " " << test2cnt << endl;
    // }

    // new variant
    // cout << "clause " << *premise << endl;
    res = pvi(iterTraits(getRewritingsIterator(_salg->getOrdering(), premise))
      .flatMap([this](pair<pair<Literal*,Term*>, TermList> arg) {
        // cout << "literal " << *arg.first.first << " rewritten " << *arg.first.second << " term " << arg.second << endl;
        return pvi(pushPairIntoRightIterator(arg, _index->getUnifications(arg.second)));
      })

    // // old variant
    // res = pvi(iterTraits(premise->iterLits())
    //   // .filter([](Literal* lit){
    //   //   return lit->ground();
    //   // })
    //   // .flatMap([](Literal* lit){
    //   //   return pvi(pushPairIntoRightIterator(lit, getUniquePersistentIterator(vi(new NonVariableIterator(lit)))));
    //   // })
    //   .flatMap([](Literal* lit){
    //     return pvi(pushPairIntoRightIterator(lit, termArgIter(lit)));
    //   })
    //   .map([](pair<Literal*, TermList> kv) { return make_pair(kv.first, kv.second.isTerm() ? kv.second.term() : nullptr); })
    //   .filter([](pair<Literal*, Term*> kv) { return kv.second!=nullptr; })
    //   .flatMap([](pair<Literal*, Term*> kv) {
    //     return pvi(pushPairIntoRightIterator(kv, getUniquePersistentIterator(vi(new NonVariableIterator(kv.second, true)))));
    //   })

    //   // Get clauses with a function definition literal whose lhs is a generalization of the rewritable subterm,
    //   // returns a pair with the original pair and the generalization result (includes substitution)
    //   .flatMap([this](pair<pair<Literal *,Term*>, TermList> arg) {
    //     return pvi(pushPairIntoRightIterator(make_pair(arg, _index->getUnifications(arg.second))));
    //   })

      //Perform forward rewriting
      .map([this, premise](pair<pair<pair<Literal*, Term*>, TermList>, TermQueryResult> arg) {
        TermQueryResult &qr = arg.second;
        return perform(
          premise, arg.first.first.first, arg.first.first.second, arg.first.second, qr.clause,
          qr.literal, qr.term, qr.substitution, true);
      }));
  // }
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
        qr.clause, qr.literal, nullptr, qr.term, premise, arg.first.first,
        arg.first.second, qr.substitution, false);
    }));

  // Remove null elements
  return pvi(iterTraits(getConcatenatedIterator(res, it))
    .filter(NonzeroFn())
    .timeTraced("induction rewriting"));
}

Clause *InductionForwardRewriting::perform(
    Clause *rwClause, Literal *rwLit, Term* rwLastRewritten, TermList rwTerm,
    Clause *eqClause, Literal *eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult)
{
  CALL("InductionForwardRewriting::perform");
  // we want the rwClause and eqClause to be active
  ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);
  ASS(!rwClause->isBackwardParamodulated() && !eqClause->isBackwardParamodulated());

  //TODO: do we need rewriting from variables?
  if (eqLHS.isVar()) {
    // static unsigned varLhsCnt = 0;
    // varLhsCnt++;
    // if (varLhsCnt % 1000 == 0) {
    //   cout << varLhsCnt << endl;
    // }
    return nullptr;
  }

  if (SortHelper::getTermSort(rwTerm, rwLit) != SortHelper::getEqualityArgumentSort(eqLit)) {
    // sorts don't match
    return nullptr;
  }

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  TermList tgtTermS = subst->apply(tgtTerm, eqIsResult);
  Literal* rwLitS = subst->apply(rwLit, !eqIsResult);
  TermList rwTermS = subst->apply(rwTerm, !eqIsResult);

  Ordering& ordering = _salg->getOrdering();
  if (Ordering::isGorGEorE(ordering.compare(tgtTermS,rwTermS))) {
    // ASS_NEQ(ordering.compare(tgtTermS,rwTermS), Ordering::INCOMPARABLE);
    return nullptr;
  }

  auto eqLastRewritten = eqClause->getLastRewrittenTerm();
  if (eqLastRewritten) {
    auto eqLastRewrittenS = subst->apply(TermList(eqLastRewritten), eqIsResult);
    auto eqLHSS = subst->apply(eqLHS, eqIsResult);
    auto comp = ordering.compare(eqLastRewrittenS, eqLHSS);
    if (comp == Ordering::Result::LESS || comp == Ordering::Result::LESS_EQ) {
      // static unsigned lastRewrittenSmallerCnt = 0;
      // lastRewrittenSmallerCnt++;
      // if (lastRewrittenSmallerCnt % 100 == 0) {
      //   cout << "lastRewrittenSmallerCnt " << lastRewrittenSmallerCnt << endl;
      // }
      return nullptr;
    }
  }

  // This inference is covered by superposition if:
  // 1. eqLit is selected in eqClause and
  // 2. rwTerm is a rewritable subterm of a selected literals of rwClause
  //    (or of rwLit if simultaneous superposition is off)
  static bool doSimS = _salg->getOptions().simulatenousSuperposition();
  // bool selected = false;
  // for (unsigned i = 0; i < eqClause->numSelected(); i++) {
  //   if ((*eqClause)[i] == eqLit) {
  //     selected = true;
  //     break;
  //   }
  // }
  // if (selected) {
  //   if (doSimS) {
  //     for (unsigned i = 0; i < rwClause->numSelected(); i++) {
  //       auto rwstit = EqHelper::getSubtermIterator((*rwClause)[i], ordering);
  //       while (rwstit.hasNext()) {
  //         if (rwTerm == rwstit.next()) {
  //           return 0;
  //         }
  //       }
  //     }
  //   } else {
  //     auto rwstit = EqHelper::getSubtermIterator(rwLit, ordering);
  //     while (rwstit.hasNext()) {
  //       if (rwTerm == rwstit.next()) {
  //         return 0;
  //       }
  //     }
  //   }
  // }

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

  for (unsigned i = 0; i < eqLength; i++) {
    Literal *curr = (*eqClause)[i];
    if (curr != eqLit) {
      Literal* currAfter = subst->apply(curr, eqIsResult);

      if (EqHelper::isEqTautology(currAfter)) {
        res->destroy();
        return 0;
      }

      (*res)[next++] = currAfter;
    }
  }
  if (!eqIsResult) {
    auto termsL = List<pair<Literal*,Term*>>::empty();
    List<pair<Literal*,Term*>>::pushFromIterator(termArgIter(rwLit).filter([rwTerm](TermList t) {
      return t.containsSubterm(rwTerm);
    })
    .map([rwLit](TermList t) {
      return make_pair(rwLit, t.term());
    }), termsL);
    auto rest = List<pair<Literal*,Term*>>::empty();
    separateMaximals(_salg->getOrdering(), termsL, rest);
    auto val = List<pair<Literal*,Term*>>::length(termsL);
    ASS_EQ(val, 1);
    rwLastRewritten = termsL->head().second;
  }
  // cout << *rwLastRewritten << endl;
  auto rwLastRewrittenS = rwLastRewritten ? subst->apply(TermList(rwLastRewritten), !eqIsResult).term() : nullptr;
  // if (rwLastRewrittenS) {
  //   cout << "rwLastRewritten for " << *res << " is " << (rwLastRewrittenS ? rwLastRewrittenS->toString() : "none") << endl
  //        << "with " << *rwClause << " and " << *eqClause << endl << endl;
  // }
  res->setLastRewrittenTerm(rwLastRewrittenS);
  res->markForwardParamodulated();
  if (eqIsResult) {
    env.statistics->forwardInductionForwardRewriting++;
  } else {
    env.statistics->backwardInductionForwardRewriting++;
  }
  auto ptr = _eqs.findPtr(make_pair(eqClause,eqLHS));
  if (!ptr) {
    _eqs.insert(make_pair(eqClause,eqLHS), 1);
  } else {
    (*ptr)++;
  }
  return res;
}
