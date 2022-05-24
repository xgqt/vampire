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

#include "InductionHelper.hpp"

#include "InductionInjectivity.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

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
    if (!InductionHelper::isInductionLiteral(lit) || lit->polarity() || !lit->isEquality()) {
      continue;
    }

    auto lhs = lit->nthArgument(0)->term();
    auto rhs = lit->nthArgument(1)->term();
    if (lhs->functor() != rhs->functor()) {
      continue;
    }

    OperatorType *type = env.signature->getFunction(lit->nthArgument(0)->term()->functor())->fnType();
    unsigned newLength = clen + type->arity() - 1;
    for (unsigned j = 0; j < type->arity(); j++) {
      if (lhs->nthArgument(j) == rhs->nthArgument(j)) {
        newLength--;
      }
    }
    Clause* resCl = new(newLength) Clause(newLength,GeneratingInference1(InferenceRule::INDUCTION_INJECTIVITY, premise));
    std::memcpy(resCl->literals(), premise->literals(), i * sizeof(Literal*));
    for (unsigned j = 0; j < type->arity(); j++) {
      if (lhs->nthArgument(j) != rhs->nthArgument(j)) {
        (*resCl)[i + j] = Literal::createEquality(false,*lhs->nthArgument(j),*rhs->nthArgument(j),type->arg(j));
      }
    }
    // cout << "INJ " << *premise << " derives " << *resCl << endl;
    std::memcpy(resCl->literals()+i+type->arity(), premise->literals()+i, (clen-i-1) * sizeof(Literal*));
    res = pvi(getConcatenatedIterator(res, getSingletonIterator(resCl)));
  }
  return res;
}

}
