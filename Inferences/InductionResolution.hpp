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
 * Defines class InductionResolution.
 */

#ifndef __InductionResolution__
#define __InductionResolution__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class InductionResolution
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InductionResolution);
  USE_ALLOCATOR(InductionResolution);

  InductionResolution() : _unitIndex(nullptr), _nonUnitIndex(nullptr) {}

  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);

private:
  LiteralIndex* _unitIndex;
  LiteralIndex* _nonUnitIndex;
};

};

#endif // __InductionResolution__
