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
 * @file InductionHelper.hpp
 * Defines class InductionHelper
 *
 */

#ifndef __InductionHelper__
#define __InductionHelper__

#include "Forwards.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/TermIndex.hpp"

#include "Saturation/Splitter.hpp"

namespace Inferences {

using namespace Indexing;
using namespace Kernel;

class InductionHelper {
public:
  CLASS_NAME(InductionHelper);
  USE_ALLOCATOR(InductionHelper);

  InductionHelper() {}
  InductionHelper(LiteralIndex* comparisonIndex, TermIndex* inductionTermIndex, Splitter* splitter)
      : _splitter(splitter), _comparisonIndex(comparisonIndex), _inductionTermIndex(inductionTermIndex) {}

  TermQueryResultIterator getLessEqual(Term* t);
  TermQueryResultIterator getLess(Term* t);
  TermQueryResultIterator getGreaterEqual(Term* t);
  TermQueryResultIterator getGreater(Term* t);
  
  TermQueryResultIterator getTQRsForInductionTerm(TermList inductionTerm);

  void callSplitterOnNewClause(Clause* c);

  static bool isIntegerComparison(Clause* c);
  static bool isIntInductionOn();
  static bool isIntInductionOneOn();
  static bool isIntInductionTwoOn();
  static bool isInductionForFiniteIntervalsOn();
  static bool isInductionForInfiniteIntervalsOn();
  static bool isStructInductionOn();
  static bool isStructInductionOneOn();
  static bool isStructInductionRecDefOn();
  static bool isInductionClause(Clause* c);
  static bool isInductionLiteral(Literal* l);
  static bool isSideLiteral(Literal* l, Clause* c);
  static bool isMainSidePair(Literal* main, Clause* mainCl, Literal* side, Clause* sideCl);
  static bool isInductionLiteral(Literal* l, Clause* cl);
  static vset<unsigned> collectInductionSkolems(Literal* l, Clause* cl);
  static vset<unsigned> collectInductionSkolems(Literal* l, const DHSet<unsigned>* info);
  static bool isInductionTermFunctor(unsigned f);
  static bool isInductionTerm(Term* t);
  static bool isIntInductionTermListInLiteral(const TermList& tl, Literal* l);
  static bool isIntegerBoundLiteral(const TermList& tl, Literal* l);
  static bool isStructInductionFunctor(unsigned f);
  static TermList* getLowerBoundForTermListFromLiteral(const TermList& tl, Literal* l);
  static TermList* getUpperBoundForTermListFromLiteral(const TermList& tl, Literal* l);

private:
  TermQueryResultIterator getComparisonMatch(bool polarity, TermList& left, TermList& right, TermList& var);

  // The following pointers can be null if splitting or integer induction is off.
  Splitter* _splitter;  // not owned
  LiteralIndex* _comparisonIndex;  // not owned
  TermIndex* _inductionTermIndex;  // not owned
};

};  // namespace Inferences

#endif /*__InductionHelper__*/
