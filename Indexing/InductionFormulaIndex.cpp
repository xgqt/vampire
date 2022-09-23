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
 * @file InductionFormulaIndex.cpp
 * Implements class InductionFormulaIndex.
 */

#include "InductionFormulaIndex.hpp"

#include "Inferences/Induction.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Inferences;

Key InductionFormulaIndex::represent(const InductionContext& context)
{
  // all literals are ground and they are unique for
  // a specific induction context, so we order them
  // and index the set of sets of literals
  // TODO: It might be good to specialize for unit literals/clauses/etc.
  Key k;
  for (const auto& kv : context._cls) {
    LiteralStack lits = kv.second;
    sort(lits.begin(), lits.end());
    k.first.push(lits);
  }
  sort(k.first.begin(), k.first.end(), [](const LiteralStack& lhs, const LiteralStack& rhs) {
    if (lhs.size() != rhs.size()) {
      return lhs.size() < rhs.size();
    }
    return lexicographical_compare(lhs.begin(), lhs.end(), rhs.begin(), rhs.end());
  });
  return k;
}

/**
 * Index an induction context or give back the entry for it.
 * @param context contains the relevant parts uniquely defining an induction formula conclusion
 * @param e is assigned the entry containing all induction formulas with matching the context
 *          and can be extended with new clausified induction formulas.
 * @param bound1 only used with integer induction to distinguish bounds from other literals
 * @param bound2 only used with integer induction to distinguish bounds from other literals
 */
bool InductionFormulaIndex::findOrInsert(const InductionContext& context, Entry*& e, Literal* bound1, Literal* bound2)
{
  CALL("InductionFormulaIndex::insert");
  ASS(!context._cls.empty());
  auto k = represent(context);
  k.second.first = bound1;
  k.second.second = bound2;
  return _map.getValuePtr(std::move(k), e);
}

void InductionFormulaIndex::makeVacuous(const InductionContext& context, Entry* e, Clause* refutation)
{
  CALL("InductionFormulaIndex::makeVacuous");
  ASS(!context._cls.empty());
  auto k = represent(context);
  k.second.first = nullptr;
  k.second.second = nullptr;
  // Entry* entry;
  // ALWAYS(!_map.getValuePtr(std::move(k), entry));
  // ASS_EQ(e,entry);
  e->_vacuous = true;
  if (context._cls.size() == 1 && context._cls.begin()->second.size() == 1) {
    // cout << "insert into index " << *context._cls.begin()->second[0] << endl;
    TermReplacement tr(getPlaceholderForTerm(context._indTerm), TermList(0,false));
    auto tlit = tr.transform(context._cls.begin()->second[0]);
    _vacuousIndex.insert(tlit, refutation);
    // _vacuousIndex.insert(context._cls.begin()->second[0], nullptr);
    auto it = _nonVacuousIndex.getGeneralizations(tlit, false, false);
    static unsigned i = 0;
    static unsigned j = 0;
    while (it.hasNext()) {
      auto qr = it.next();
      i++;
    }
    j++;
    if (j % 1000 == 0) {
      cout << i << " generalizations found" << endl;
    }
  }
}

void InductionFormulaIndex::makeNonVacuous(const InductionContext& context)
{
  CALL("InductionFormulaIndex::makeNonVacuous");
  ASS(!context._cls.empty());
  auto k = represent(context);
  k.second.first = nullptr;
  k.second.second = nullptr;
  if (context._cls.size() == 1 && context._cls.begin()->second.size() == 1) {
    TermReplacement tr(getPlaceholderForTerm(context._indTerm), TermList(0,false));
    auto tlit = tr.transform(context._cls.begin()->second[0]);
    _nonVacuousIndex.insert(tlit, nullptr);
  }
}

bool InductionFormulaIndex::isVacuous(Literal* lit, MiniSaturation* ms)
{
  CALL("InductionFormulaIndex::isVacuous");
  // cout << "check vacuousness " << *lit << endl; 
  auto it = _vacuousIndex.getInstances(lit, false, false);
  return it.hasNext();
}


}
