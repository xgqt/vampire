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
 * @file MiniSaturation.cpp
 * Implementing MiniSaturation class.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Timer.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/System.hpp"
#include "Lib/STL.hpp"

#include "Indexing/LiteralIndexingStructure.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/KBO.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Unit.hpp"

#include "Inferences/InterpretedEvaluation.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/PushUnaryMinus.hpp"
#include "Inferences/Cancellation.hpp"
#include "Inferences/GaussianVariableElimination.hpp"
#include "Inferences/EquationalTautologyRemoval.hpp"
#include "Inferences/Condensation.hpp"
#include "Inferences/FastCondensation.hpp"
#include "Inferences/DistinctEqualitySimplifier.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/BackwardDemodulation.hpp"
#include "Inferences/BackwardSubsumptionResolution.hpp"
#include "Inferences/BackwardSubsumptionDemodulation.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/EqualityFactoring.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/BoolEqToDiseq.hpp"
#include "Inferences/ExtensionalityResolution.hpp"
#include "Inferences/FOOLParamodulation.hpp"
#include "Inferences/Injectivity.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/ForwardDemodulation.hpp"
#include "Inferences/ForwardLiteralRewriting.hpp"
#include "Inferences/ForwardSubsumptionAndResolution.hpp"
#include "Inferences/ForwardSubsumptionDemodulation.hpp"
#include "Inferences/GlobalSubsumption.hpp"
#include "Inferences/HyperSuperposition.hpp"
#include "Inferences/InnerRewriting.hpp"
#include "Inferences/TermAlgebraReasoning.hpp"
#include "Inferences/SLQueryBackwardSubsumption.hpp"
#include "Inferences/Superposition.hpp"
#include "Inferences/ArgCong.hpp"
#include "Inferences/NegativeExt.hpp"
#include "Inferences/Narrow.hpp"
#include "Inferences/PrimitiveInstantiation.hpp"
#include "Inferences/Choice.hpp"
#include "Inferences/ElimLeibniz.hpp"
#include "Inferences/SubVarSup.hpp"
#include "Inferences/CNFOnTheFly.hpp"
//#include "Inferences/RenamingOnTheFly.hpp"
#include "Inferences/URResolution.hpp"
#include "Inferences/Instantiation.hpp"
#include "Inferences/TheoryInstAndSimp.hpp"
#include "Inferences/Induction.hpp"
#include "Inferences/ArithmeticSubtermGeneralization.hpp"
#include "Inferences/TautologyDeletionISE.hpp"
#include "Inferences/CombinatorDemodISE.hpp"
#include "Inferences/CombinatorNormalisationISE.hpp"
#include "Inferences/BoolSimp.hpp"
#include "Inferences/CasesSimp.hpp"
#include "Inferences/Cases.hpp"

#include "Saturation/ExtensionalityClauseContainer.hpp"

#include "Shell/AnswerExtractor.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Splitter.hpp"

#include "ConsequenceFinder.hpp"
#include "LabelFinder.hpp"
#include "Splitter.hpp"
#include "SymElOutput.hpp"
#include "MiniSaturation.hpp"
#include "ManCSPassiveClauseContainer.hpp"
#include "AWPassiveClauseContainer.hpp"
#include "InductionAWPassiveClauseContainer.hpp"
#include "PredicateSplitPassiveClauseContainer.hpp"
#include "Discount.hpp"
#include "LRS.hpp"
#include "Otter.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;

/** Print information changes in clause containers */
#define REPORT_CONTAINERS 0
/** Print information about performed forward simplifications */
#define REPORT_FW_SIMPL 0
/** Print information about performed backward simplifications */
#define REPORT_BW_SIMPL 0

/**
 * Create a MiniSaturation object
 *
 * The @b passiveContainer object will be used as a passive clause container, and
 * @b selector object to select literals before clauses are activated.
 */
MiniSaturation::MiniSaturation(Problem& prb, const Options& opt)
  : SaturationAlgorithm(prb, opt, false)
{
  _passive->detach();
  _passive = std::make_unique<AWPassiveClauseContainer>(true, opt, "test");
  _passive->attach(this);
  // _passive->addedEvent.subscribe(this, &MiniSaturation::onPassiveAdded);
  // _passive->removedEvent.subscribe(this, &MiniSaturation::passiveRemovedHandler);
  // _passive->selectedEvent.subscribe(this, &MiniSaturation::onPassiveSelected);
}

void MiniSaturation::initMini(ClauseIterator& it)
{
  unsigned i = 0;
  while (it.hasNext()) {
    Clause* cl=Clause::fromClause(it.next());
    i++;
    // cout << "input " << i << endl;
    addInputSOSClause(cl);
    // addNewClause(cl);
  }
  // cout << i << " clauses added" << endl;
}

/**
 * @since 05/05/2013 Manchester, splitting changed to new values
 * @author Andrei Voronkov
 */
MiniSaturation* MiniSaturation::createFromOptions(Problem& prb, const Options& opt, IndexManager* indexMgr)
{
  CALL("MiniSaturation::createFromOptions");

  MiniSaturation* res=new MiniSaturation(prb, opt);
  res->setIndexManager(SmartPtr<IndexManager>(new IndexManager(res)));
  res->_answerLiteralManager = AnswerLiteralManager::getInstance();

  // if(opt.splitting()){
  //   res->_splitter = new Splitter();
  // }

  // create generating inference engine
  CompositeGIE* gie=new CompositeGIE();

  if (prb.hasEquality()) {
    gie->addFront(new EqualityFactoring());
    gie->addFront(new EqualityResolution());
    if(env.options->superposition()){
      gie->addFront(new Superposition());
    }
  }

  gie->addFront(new Factoring());
  if (opt.binaryResolution()) {
    gie->addFront(new BinaryResolution());
  }
  if(prb.hasEquality() && env.signature->hasTermAlgebras()) {
    if (opt.termAlgebraCyclicityCheck() == Options::TACyclicityCheck::RULE) {
      gie->addFront(new AcyclicityGIE());
    } else if (opt.termAlgebraCyclicityCheck() == Options::TACyclicityCheck::RULELIGHT) {
      gie->addFront(new AcyclicityGIE1());
    }
    if (opt.termAlgebraInferences()) {
      gie->addFront(new InjectivityGIE());
    }
  }

  CompositeSGI* sgi = new CompositeSGI();
  sgi->push(gie);
  res->setGeneratingInferenceEngine(sgi);

  res->setImmediateSimplificationEngine(createISE(prb, opt, res->getOrdering()));
  if (prb.hasEquality()) {
    // NOTE:
    // fsd should be performed after forward subsumption,
    // because every successful forward subsumption will lead to a (useless) match in fsd.
    if (opt.forwardSubsumptionDemodulation()) {
      res->addForwardSimplifierToFront(new ForwardSubsumptionDemodulation(false));
    }
  }
  if (prb.hasEquality()) {
    switch(opt.forwardDemodulation()) {
    case Options::Demodulation::ALL:
    case Options::Demodulation::PREORDERED:
      if(opt.combinatorySup()){
        res->addForwardSimplifierToFront(new ForwardDemodulationImpl<true>());
      } else {
        res->addForwardSimplifierToFront(new ForwardDemodulationImpl<false>());
      }
      break;
    case Options::Demodulation::OFF:
      break;
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
    }
  }
  if (opt.forwardSubsumption()) {
    if (opt.forwardSubsumptionResolution()) {
      //res->addForwardSimplifierToFront(new CTFwSubsAndRes(true));
      res->addForwardSimplifierToFront(new ForwardSubsumptionAndResolution(true));
    }
    else {
      //res->addForwardSimplifierToFront(new CTFwSubsAndRes(false));
      res->addForwardSimplifierToFront(new ForwardSubsumptionAndResolution(false));
    }
  }
  else if (opt.forwardSubsumptionResolution()) {
    USER_ERROR("Forward subsumption resolution requires forward subsumption to be enabled.");
  }

  // create backward simplification engine
  if (prb.hasEquality()) {
    switch(opt.backwardDemodulation()) {
    case Options::Demodulation::ALL:
    case Options::Demodulation::PREORDERED:
      res->addBackwardSimplifierToFront(new BackwardDemodulation());
      break;
    case Options::Demodulation::OFF:
      break;
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
    }
  }
  if (prb.hasEquality() && opt.backwardSubsumptionDemodulation()) {
    res->addBackwardSimplifierToFront(new BackwardSubsumptionDemodulation());
  }
  if (opt.backwardSubsumption() != Options::Subsumption::OFF) {
    bool byUnitsOnly=opt.backwardSubsumption()==Options::Subsumption::UNIT_ONLY;
    res->addBackwardSimplifierToFront(new SLQueryBackwardSubsumption(byUnitsOnly));
  }
  if (opt.backwardSubsumptionResolution() != Options::Subsumption::OFF) {
    bool byUnitsOnly=opt.backwardSubsumptionResolution()==Options::Subsumption::UNIT_ONLY;
    res->addBackwardSimplifierToFront(new BackwardSubsumptionResolution(byUnitsOnly));
  }

  return res;
} // MiniSaturation::createFromOptions


/**
 * Create local clause simplifier for problem @c prb according to options @c opt
 */
ImmediateSimplificationEngine* MiniSaturation::createISE(Problem& prb, const Options& opt, Ordering& ordering)
{
  CALL("MainLoop::createImmediateSE");

  CompositeISE* res=new CompositeISE();

  if(prb.hasEquality() && opt.equationalTautologyRemoval()) {
    res->addFront(new EquationalTautologyRemoval());
  }

  if(prb.hasEquality() && env.signature->hasTermAlgebras()) {
    if (opt.termAlgebraInferences()) {
      res->addFront(new DistinctnessISE());
      res->addFront(new InjectivityISE());
      res->addFront(new NegativeInjectivityISE());
    }
  }
  if(prb.hasEquality()) {
    res->addFront(new TrivialInequalitiesRemovalISE());
  }
  res->addFront(new TautologyDeletionISE());
  if(env.options->newTautologyDel()){
    res->addFront(new TautologyDeletionISE2());
  }
  res->addFront(new DuplicateLiteralRemovalISE());

  return res;
}

