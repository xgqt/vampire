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
 * @file CrossInductionElimination.hpp
 * Defines class CrossInductionElimination.
 */

#ifndef __CrossInductionElimination__
#define __CrossInductionElimination__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Indexing/LiteralIndex.hpp"

namespace Inferences {

class CrossInductionElimination
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(CrossInductionElimination);
  USE_ALLOCATOR(CrossInductionElimination);

  Clause* simplify(Clause* cl) override;
};

};

#endif /* __CrossInductionElimination__ */
