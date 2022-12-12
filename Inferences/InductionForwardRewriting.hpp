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
 * @file InductionForwardRewriting.hpp
 * Defines class InductionForwardRewriting.
 */

#ifndef __InductionForwardRewriting__
#define __InductionForwardRewriting__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {

class InductionForwardRewriting
  : public GeneratingInferenceEngine
  {
public:
  CLASS_NAME(InductionForwardRewriting);
  USE_ALLOCATOR(InductionForwardRewriting);

  void attach(SaturationAlgorithm* salg) override
  {
    GeneratingInferenceEngine::attach(salg);
    _index=static_cast<RewritingLHSIndex*>(
      _salg->getIndexManager()->request(REWRITING_LHS_INDEX));
    _tindex=static_cast<RewritingSubtermIndex*>(
      _salg->getIndexManager()->request(REWRITING_SUBTERM_INDEX));
  }
  void detach() override
  {
    _index = nullptr;
    _tindex = nullptr;
    _salg->getIndexManager()->release(REWRITING_SUBTERM_INDEX);
    _salg->getIndexManager()->release(REWRITING_LHS_INDEX);
    GeneratingInferenceEngine::detach();
  }
  ClauseIterator generateClauses(Clause *premise) override;
  static VirtualIterator<pair<pair<Literal*,Term*>,TermList>> getRewritingsIterator(Ordering& ord, Clause* premise);
  void output();

private:
  Clause *perform(
    Clause *rwClause, Literal *rwLiteral, Term* rwLastRewritten, TermList rwTerm,
    Clause *eqClause, Literal *eqLiteral, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult);

  RewritingLHSIndex* _index;
  RewritingSubtermIndex* _tindex;
  DHMap<pair<Clause*,TermList>, unsigned> _eqs;
};

}; // namespace Inferences

#endif /* __InductionForwardRewriting__ */
