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
 * @file CrossInductionElimination.cpp
 * Implements class CrossInductionElimination.
 */

#include "Saturation/SaturationAlgorithm.hpp"
#include "InductionRemodulation.hpp"

#include "CrossInductionElimination.hpp"

namespace Inferences
{

Clause* CrossInductionElimination::simplify(Clause* cl)
{
  CALL("CrossInductionElimination::simplify");

  Clause* res = cl;
  for (unsigned li = 0; li < cl->length(); li++) {
    if (_salg->getRemodulationManager()->isConflicting((*cl)[li])) {
      env.statistics->crossInductionElimination++;
      return nullptr;
    }
  }

  return res;
}

}
