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
 * @file InductionInjectivity.hpp
 * Defines class InductionInjectivity
 *
 */

#ifndef __InductionInjectivity__
#define __InductionInjectivity__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

class InductionInjectivity
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InductionInjectivity);
  USE_ALLOCATOR(InductionInjectivity);

  ClauseIterator generateClauses(Clause* premise) override;
};

}

#endif /*__InductionInjectivity__*/
