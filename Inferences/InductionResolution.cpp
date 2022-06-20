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
 * @file InductionResolution.cpp
 * Implements class InductionResolution.
 */

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "InductionResolution.hpp"
#include "InductionHelper.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void InductionResolution::attach(SaturationAlgorithm* salg)
{
  CALL("InductionResolution::attach");
  GeneratingInferenceEngine::attach(salg);

  _unitIndex = static_cast<LiteralIndex*> (
	  _salg->getIndexManager()->request(INDUCTION_UNIT_LITERAL_INDEX) );
  _nonUnitIndex = static_cast<LiteralIndex*> (
	  _salg->getIndexManager()->request(INDUCTION_NON_GROUND_LITERAL_INDEX) );
}

void InductionResolution::detach()
{
  CALL("InductionResolution::detach");
  _unitIndex = 0;
  _salg->getIndexManager()->release(INDUCTION_NON_GROUND_LITERAL_INDEX);
  _nonUnitIndex = 0;
  _salg->getIndexManager()->release(INDUCTION_UNIT_LITERAL_INDEX);
  GeneratingInferenceEngine::detach();
}

ClauseIterator concatClause(const ClauseIterator& res, const LiteralStack& lits, const UnitStack& prems)
{
  for (const auto& lit : lits) {
    if (!InductionHelper::isInductionLiteral(lit)) {
      return res;
    }
  }
  auto pl = UnitList::empty();
  for (const auto& p : prems) {
    UnitList::push(p,pl);
  }
  ASS_GE(UnitList::length(pl), 2);
  Inference inf(GeneratingInferenceMany(InferenceRule::INDUCTION_RESOLUTION, pl));
  Clause* newCl = Clause::fromStack(lits, inf);
  env.statistics->inductionResolution++;
  // if (!newCl->isGround()) {
  //   return res;
  // }
  // cout << *newCl << endl;
  // cout << "premises " << endl;
  // UnitList::Iterator it(pl);
  // while (it.hasNext()) {
  //   cout << *it.next() << endl;
  // }
  // cout << endl;
  return pvi(getConcatenatedIterator(res,getSingletonIterator(newCl)));
}

ClauseIterator InductionResolution::generateClauses(Clause* cl)
{
  CALL("InductionResolution::generateClauses");
  ASS(_salg->getSplitter());

  unsigned clen = cl->size();
  ClauseIterator res = ClauseIterator::getEmpty();
  Stack<tuple<LiteralStack,unsigned,UnitStack>> todo;
  if (cl->isGround() && clen == 1) {
    auto it = _nonUnitIndex->getUnifications((*cl)[0], true, true);
    while (it.hasNext()) {
      auto qr = it.next();
      auto ns = qr.clause->numSelected();
      LiteralStack lits;
      UnitStack prems;
      for (unsigned i = 0; i < qr.clause->length(); i++) {
        auto curr = (*qr.clause)[i];
        if (curr != qr.literal) {
          lits.push(qr.substitution->applyTo(curr,true));
        } else {
          ASS_GE(i,ns);
        }
      }
      prems.push(qr.clause);
      prems.push(cl);
      if (ns == lits.size()) {
        res = concatClause(res, lits, prems);
      } else {
        todo.push(make_tuple(lits,ns,prems));
      }
    }
  } else if (isFormulaTransformation(cl->inference().rule())) {
    ASS(!cl->isGround());
    auto ns = cl->numSelected();
    if (ns != clen) {
      LiteralStack lits(clen);
      UnitStack prems;
      for (unsigned i = 0; i < clen; i++) {
        lits.push((*cl)[i]);
      }
      prems.push(cl);
      todo.push(make_tuple(lits,ns,prems));
    }
  }

  while (todo.isNonEmpty()) {
    auto t = todo.pop();
    auto lits = get<0>(t);
    auto idx = get<1>(t);
    auto prems = get<2>(t);
    auto rlit = lits[idx];
    auto it = _unitIndex->getUnifications(rlit, true, true);
    while (it.hasNext()) {
      auto qr = it.next();
      ASS_EQ(qr.clause->length(),1);
      LiteralStack nLits;
      auto nPrems = prems;
      nPrems.push(qr.clause);
      for (unsigned i = 0; i < lits.size(); i++) {
        if (i != idx) {
          nLits.push(qr.substitution->applyTo(lits[i],false));
        }
      }
      if (idx == lits.size()-1) {
        res = concatClause(res, nLits, nPrems);
      } else {
        todo.push(make_tuple(nLits,idx,nPrems));
      }
    }
  }

  return res;
}

}
