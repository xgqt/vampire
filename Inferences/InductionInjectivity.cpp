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
 * @file InductionInjectivity.cpp
 * Implements class InductionInjectivity.
 */

#include "Lib/Metaiterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/TermIterators.hpp"

#include "InductionHelper.hpp"

#include "InductionInjectivity.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

void InductionInjectivity::attach(SaturationAlgorithm* salg)
{
  CALL("InductionInjectivity::attach");
  GeneratingInferenceEngine::attach(salg);
  _index = static_cast<LiteralIndex*>(_salg->getIndexManager()->request(GENERATING_SUBST_TREE));
}

void InductionInjectivity::detach()
{
  CALL("InductionInjectivity::detach");
  _index = nullptr;
  _salg->getIndexManager()->release(GENERATING_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}

vset<unsigned> getSkolems(Term* t) {
  vset<unsigned> res;
  NonVariableNonTypeIterator it(t, true);
  while (it.hasNext()) {
    auto trm = it.next();
    if (env.signature->getFunction(trm.term()->functor())->skolem()) {
      res.insert(trm.term()->functor());
    }
  }
  return res;
}

bool skolemCheck(Term* left, Term* right) {
  vset<unsigned> lsk = getSkolems(left);
  vset<unsigned> rsk = getSkolems(right);
  vset<unsigned> is;
  set_intersection(lsk.begin(), lsk.end(), rsk.begin(), rsk.end(), inserter(is, is.end()));
  return !is.empty();
}

ClauseIterator InductionInjectivity::generateClauses(Clause* premise)
{
  CALL("InductionInjectivity::generateClauses");
  ClauseIterator res = ClauseIterator::getEmpty();

  if (!InductionHelper::isInductionClause(premise)) {
    return res;
  }

  auto clen = premise->length();
  for (unsigned i = 0; i < clen; i++) {
    auto lit = (*premise)[i];
    if (!lit->ground()) {
      continue;
    }

    // handle equalities
    if (lit->isEquality()) {
      if (!InductionHelper::isInductionLiteral(lit) || lit->isPositive()) {
        continue;
      }

      auto lhs = lit->nthArgument(0)->term();
      auto rhs = lit->nthArgument(1)->term();
      if (lhs->functor() != rhs->functor()) {
        continue;
      }

      OperatorType *type = env.signature->getFunction(lit->nthArgument(0)->term()->functor())->fnType();
      unsigned newLength = clen + type->arity() - 1;
      bool skip = false;
      for (unsigned j = 0; j < type->arity(); j++) {
        if (*lhs->nthArgument(j) == *rhs->nthArgument(j)) {
          newLength--;
          continue;
        }
        if (!skolemCheck(lhs->nthArgument(j)->term(), rhs->nthArgument(j)->term())) {
          skip = true;
          break;
        }
      }
      if (skip) {
        continue;
      }
      Clause* resCl = new(newLength) Clause(newLength,GeneratingInference1(InferenceRule::INDUCTION_INJECTIVITY, premise));
      unsigned next = 0;
      // std::memcpy(resCl->literals(), premise->literals(), i * sizeof(Literal*));
      for (unsigned j = 0; j < type->arity(); j++) {
        if (*lhs->nthArgument(j) != *rhs->nthArgument(j)) {
          (*resCl)[next++] = Literal::createEquality(false,*lhs->nthArgument(j),*rhs->nthArgument(j),type->arg(j));
        }
      }
      // std::memcpy(resCl->literals()+i+type->arity(), premise->literals()+i, (clen-i-1) * sizeof(Literal*));
      for (unsigned j = 0; j < clen; j++) {
        auto curr = (*premise)[j];
        if (lit == curr) { continue; }
        (*resCl)[next++] = curr;
      }
      ASS_EQ(next,newLength);
      // cout << "INJ " << *premise << " derives " << *resCl << endl;
      res = pvi(getConcatenatedIterator(res, getSingletonIterator(resCl)));
    }
    // handle predicates
    else {
      TermStack gargs;
      for (unsigned i = 0; i < lit->arity(); i++) {
        gargs.push(TermList(i,false));
      }
      auto glit = Literal::create(lit, gargs.begin());
      auto it = _index->getUnifications(glit, true, false);
      while (it.hasNext()) {
        auto qr = it.next();
        auto other = qr.literal;
        if (!other->ground()) {
          continue;
        }

        OperatorType *type = env.signature->getPredicate(lit->functor())->predType();
        unsigned dlen = qr.clause->length();
        unsigned newLength = clen + dlen + type->arity() - 2;
        bool skip = false;
        for (unsigned j = 0; j < type->arity(); j++) {
          if (*lit->nthArgument(j) == *other->nthArgument(j)) {
            newLength--;
            continue;
          }
          if (!skolemCheck(lit->nthArgument(j)->term(), other->nthArgument(j)->term())) {
            skip = true;
            break;
          }
        }
        if (skip) {
          continue;
        }
        Clause* resCl = new(newLength) Clause(newLength,GeneratingInference2(InferenceRule::INDUCTION_INJECTIVITY, premise, qr.clause));
        unsigned next = 0;
        // std::memcpy(resCl->literals(), premise->literals(), i * sizeof(Literal*));
        for (unsigned j = 0; j < type->arity(); j++) {
          if (*lit->nthArgument(j) != *other->nthArgument(j)) {
            (*resCl)[next++] = Literal::createEquality(false,*lit->nthArgument(j),*other->nthArgument(j),type->arg(j));
          }
        }
        for (unsigned j = 0; j < clen; j++) {
          auto curr = (*premise)[j];
          if (lit == curr) { continue; }
          (*resCl)[next++] = curr;
        }
        // std::memcpy(resCl->literals()+i+type->arity(), premise->literals()+i, (clen-i-1) * sizeof(Literal*));
        ASS_GE(newLength,dlen);
        for (unsigned j = 0; j < dlen; j++) {
          auto curr = (*qr.clause)[j];
          if (other == curr) { continue; }
          (*resCl)[next++] = curr;
        }
        ASS_EQ(next,newLength);
        // std::memcpy(resCl->literals()+(newLength-dlen), qr.clause->literals(), dlen * sizeof(Literal*));
        // cout << "INJ " << *premise << endl << " and " << *other << endl << " derive " << *resCl << endl << endl;
        res = pvi(getConcatenatedIterator(res, getSingletonIterator(resCl)));
        env.statistics->inductionInjectivity++;
      }
    }
  }
  return res;
}

}
