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
 * @file MiniSaturation.hpp
 * Defines class MiniSaturation
 *
 */

#ifndef __MiniSaturation__
#define __MiniSaturation__

#include "Forwards.hpp"

#include "SaturationAlgorithm.hpp"
#include "Shell/AnswerExtractor.hpp"

#if VDEBUG
#include<iostream>
#endif

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Inferences;

class MiniSaturation : public SaturationAlgorithm
{
public:
  CLASS_NAME(MiniSaturation);
  USE_ALLOCATOR(MiniSaturation);

  static MiniSaturation* createFromOptions(Problem& prb, const Options& opt, IndexManager* indexMgr=0);
  static ImmediateSimplificationEngine* createISE(Problem& prb, const Options& opt, Ordering& ordering);
  ClauseContainer* getSimplifyingClauseContainer() override
  {
    return _active;
  }
  bool getAnswers(Clause* refutation, Stack<TermList>& answer) {
    if (!_answerLiteralManager->tryGetAnswer(refutation, answer)) {
      ConjunctionGoalAnswerExractor cge;
      if (!cge.tryGetAnswer(refutation, answer)) {
        return false;
      }
    }
    return true;
  }

  MiniSaturation(Problem& prb, const Options& opt);
  void initMini(ClauseIterator& it);
};

};

#endif /*__MiniSaturation__*/
