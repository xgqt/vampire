/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "InductionPreprocessor.hpp"
#include "Inferences/InductionHelper.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Signature.hpp"

#include "Lib/Hash.hpp"

using namespace Inferences;
using namespace Kernel;
using namespace Lib;

namespace Shell {

void FnDefHandler::handleClause(Clause* c, unsigned fi, bool reversed)
{
  CALL("FnDefHandler::handleClause");

  auto lit = (*c)[fi];
  auto trueFun = lit->isEquality();
  Term* header;
  vvector<Term*> recursiveCalls;
  unsigned fn;

  if (trueFun) {
    ASS(lit->isPositive());
    ASS(lit->nthArgument(reversed ? 1 : 0)->isTerm());
    header = lit->nthArgument(reversed ? 1 : 0)->term();
    TermList body = *lit->nthArgument(reversed ? 0 : 1);
    ASS(lit->nthArgument(reversed ? 1 : 0)->containsAllVariablesOf(body));

    static const bool fnrw = env.options->functionDefinitionRewriting();
    if (fnrw) {
      _is->insert(TermList(header), lit, c);
    }

    fn = header->functor();
    InductionPreprocessor::processCase(fn, body, recursiveCalls);
  } else {
    // look for other literals with the same top-level functor
    fn = lit->functor();
    header = lit->isPositive() ? lit : Literal::complementaryLiteral(lit);
    for(unsigned i = 0; i < c->length(); i++) {
      if (fi != i) {
        Literal* curr = (*c)[i];
        if (!curr->isEquality() && fn == curr->functor()) {
          recursiveCalls.push_back(curr->isPositive() ? curr : Literal::complementaryLiteral(curr));
        }
      }
    }
  }
  auto p = make_pair(fn, trueFun);
  auto templIt = _templates.find(p);
  if (templIt == _templates.end()) {
    templIt = _templates.insert(make_pair(p, new InductionTemplate(header))).first;
  }

  templIt->second->addBranch(std::move(recursiveCalls), std::move(header));
}

void FnDefHandler::finalize()
{
  CALL("FnDefHandler::finalize");

  for (auto it = _templates.begin(); it != _templates.end();) {
    if (!it->second->finalize()) {
      if (env.options->showInduction()) {
        env.beginOutput();
        env.out() << "% Warning: " << it->second << " discarded" << endl;
        env.endOutput();
      }
      it = _templates.erase(it);
      continue;
    } else {
      if (env.options->showInduction()){
        env.beginOutput();
        if (it->first.second) {
          env.out() << "[Induction] function: " << env.signature->getFunction(it->first.first)->name() << endl;
        } else {
          env.out() << "[Induction] predicate: " << env.signature->getPredicate(it->first.first)->name() << endl;
        }
        env.out() << ", with induction template: " << *it->second << endl;
        env.endOutput();
      }
      it++;
    }
  }
}

ostream& operator<<(ostream& out, const InductionTemplate::Branch& branch)
{
  if (!branch._recursiveCalls.empty()) {
    out << "(";
    unsigned n = 0;
    for (const auto& r : branch._recursiveCalls) {
      out << *r;
      if (++n < branch._recursiveCalls.size()) {
        out << " & ";
      }
    }
    out << ") => ";
  }
  out << *branch._header;
  return out;
}

bool InductionTemplate::finalize() {
  CALL("InductionTemplate::finalize");

  if (!checkWellFoundedness() || !checkUsefulness()) {
    return false;
  }

  checkWellDefinedness();
  return true;
}

void InductionTemplate::checkWellDefinedness()
{
  CALL("InductionTemplate::checkWellDefinedness");

  vvector<Term*> cases;
  for (auto& b : _branches) {
    cases.push_back(b._header);
  }
  vvector<vvector<TermList>> missingCases;
  InductionPreprocessor::checkWellDefinedness(cases, missingCases);

  if (!missingCases.empty()) {
    if (env.options->showInduction()) {
      env.beginOutput();
      env.out() << "% Warning: adding missing cases to template " << *this;
    }
    for (const auto& m : missingCases) {
      Stack<TermList> args;
      ASS_EQ(m.size(), _arity);
      for(const auto& arg : m) {
        args.push(arg);
      }
      Term* t;
      if (_isLit) {
        t = Literal::create(static_cast<Literal*>(_branches[0]._header), args.begin());
      } else {
        t = Term::create(_functor, _arity, args.begin());
      }
      addBranch(vvector<Term*>(), std::move(t));
    }
    if (env.options->showInduction()) {
      env.out() << ". New template is " << *this << endl;
      env.endOutput();
    }
  }
}

bool InductionTemplate::matchesTerm(Term* t, vvector<Term*>& inductionTerms) const
{
  CALL("InductionTemplate::matchesTerm");
  ASS(t->ground());
  inductionTerms.clear();
  for (unsigned i = 0; i < t->arity(); i++) {
    auto arg = t->nthArgument(i)->term();
    auto f = arg->functor();
    if (_indPos[i] && InductionHelper::isInductionTermFunctor(f)) {
      if (!InductionHelper::isStructInductionOn() || !InductionHelper::isStructInductionFunctor(f)) {
        return false;
      }
      auto it = std::find(inductionTerms.begin(),inductionTerms.end(),arg);
      if (it != inductionTerms.end()) {
        return false;
      }
      inductionTerms.push_back(arg);
    }
  }
  return !inductionTerms.empty();
}

bool InductionTemplate::Branch::contains(const InductionTemplate::Branch& other) const
{
  CALL("InductionTemplate::Branch::contains");

  RobSubstitution subst;
  if (!subst.match(TermList(_header), 0, TermList(other._header), 1)) {
    return false;
  }

  for (auto recCall2 : other._recursiveCalls) {
    bool found = false;
    for (auto recCall1 : _recursiveCalls) {
      Term* l1;
      Term* l2;
      if (_header->isLiteral()) {
        l1 = subst.apply(static_cast<Literal*>(recCall1), 0);
        l2 = subst.apply(static_cast<Literal*>(recCall2), 1);
      } else {
        l1 = subst.apply(TermList(recCall1), 0).term();
        l2 = subst.apply(TermList(recCall2), 1).term();
      }
      if (l1 == l2) {
        found = true;
        break;
      }
    }
    if (!found) {
      return false;
    }
  }
  return true;
}

bool InductionTemplate::checkUsefulness() const
{
  CALL("InductionTemplate::checkUsefulness");

  // discard templates without inductive argument positions:
  // this happens either when there are no recursive calls
  // or none of the arguments change in any recursive call
  bool discard = true;
  for (const auto& p : _indPos) {
    if (p) {
      discard = false;
    }
  }
  if (discard) {
    auto t = _branches.begin()->_header;
    if (env.options->showInduction()) {
      env.beginOutput();
      env.out() << "% Warning: template for "
                << (t->isLiteral() ? "predicate " : "function ")
                << (t->isLiteral() ? static_cast<Literal*>(t)->predicateName() : t->functionName())
                << " is discarded because it is not useful" << endl;
      env.endOutput();
    }
  }
  return !discard;
}

VList* getVariables(TermList t) {
  if (t.isVar()) {
    return VList::singleton(t.var());
  }
  return t.freeVariables();
}

bool InductionTemplate::checkWellFoundedness()
{
  CALL("InductionTemplate::checkWellFoundedness");

  // fill in bit vector of induction variables
  vvector<pair<Term*, Term*>> relatedTerms;
  for (auto& b : _branches) {
    for (auto& r : b._recursiveCalls) {
      relatedTerms.push_back(make_pair(b._header, r));
      for (unsigned i = 0; i < _arity; i++) {
        if (env.signature->isTermAlgebraSort(_type->arg(i))) {
          _indPos[i] = _indPos[i] || (*b._header->nthArgument(i) != *r->nthArgument(i));
        }
      }
    }
  }
  return InductionPreprocessor::checkWellFoundedness(relatedTerms);
}

InductionTemplate::InductionTemplate(const Term* t)
    : _functor(t->functor()), _arity(t->arity()), _isLit(t->isLiteral()),
    _type(_isLit ? env.signature->getPredicate(_functor)->predType()
                 : env.signature->getFunction(_functor)->fnType()),
    _branches(), _indPos(_arity, false) {}

void InductionTemplate::addBranch(vvector<Term*>&& recursiveCalls, Term*&& header)
{
  CALL("InductionTemplate::addBranch");

  ASS(header->arity() == _arity && header->isLiteral() == _isLit && header->functor() == _functor);
  Branch branch(std::move(recursiveCalls), std::move(header));
  for (auto b : _branches) {
    if (b.contains(branch)) {
      return;
    }
  }
  _branches.erase(remove_if(_branches.begin(), _branches.end(),
  [&branch](const Branch& b) {
    return branch.contains(b);
  }), _branches.end());
  _branches.push_back(std::move(branch));
}

ostream& operator<<(ostream& out, const InductionTemplate& templ)
{
  out << "Branches: ";
  unsigned n = 0;
  for (const auto& b : templ._branches) {
    out << b;
    if (++n < templ._branches.size()) {
      out << "; ";
    }
  }
  out << " with positions: (";
  for (unsigned i = 0; i < templ._arity; i++) {
    if (templ._indPos[i]) {
      out << "i";
    } else {
      out << "0";
    }
    if (i+1 < templ._arity) {
      out << ",";
    }
  }
  out << ")";
  return out;
}

void InductionPreprocessor::processCase(const unsigned fn, TermList body, vvector<Term*>& recursiveCalls)
{
  CALL("InductionPreprocessor::processCase");

  // If we arrived at a variable, nothing to do
  if (!body.isTerm()) {
    return;
  }

  NonVariableIterator it(body.term(), true);
  while (it.hasNext()) {
    auto st = it.next();
    if (st.term()->functor() == fn) {
      recursiveCalls.push_back(st.term());
    }
  }
}

bool checkWellFoundednessHelper(const vvector<pair<Term*,Term*>>& relatedTerms,
  const vset<unsigned>& indices, const vset<unsigned>& positions)
{
  CALL("checkWellFoundednessHelper");

  if (indices.empty()) {
    return true;
  }
  if (positions.empty()) {
    return false;
  }
  for (const auto& p : positions) {
    vset<unsigned> newInd;
    bool canOrder = true;
    for (const auto& i : indices) {
      auto arg1 = *relatedTerms[i].first->nthArgument(p);
      auto arg2 = *relatedTerms[i].second->nthArgument(p);
      if (arg1 == arg2) {
        newInd.insert(i);
      } else if (!arg1.containsSubterm(arg2)) {
        canOrder = false;
        break;
      }
    }
    if (canOrder) {
      auto newPos = positions;
      newPos.erase(p);
      if (checkWellFoundednessHelper(relatedTerms, newInd, newPos)) {
        return true;
      }
    }
  }
  return false;
}

bool InductionPreprocessor::checkWellFoundedness(const vvector<pair<Term*,Term*>>& relatedTerms)
{
  CALL("static InductionPreprocessor::checkWellFoundedness");

  if (relatedTerms.empty()) {
    return true;
  }
  auto t = relatedTerms[0].first;
  bool isFun = !t->isLiteral();
  auto fn = t->functor();
  auto arity = t->arity();
  OperatorType* type;
  if (isFun) {
    type = env.signature->getFunction(fn)->fnType();
  } else {
    type = env.signature->getPredicate(fn)->predType();
  }
  vset<unsigned> positions;
  for (unsigned i = 0; i < arity; i++) {
    if (env.signature->isTermAlgebraSort(type->arg(i))) {
      positions.insert(i);
    }
  }
  vset<unsigned> indices;
  for (unsigned i = 0; i < relatedTerms.size(); i++) {
    indices.insert(i);
  }
  return checkWellFoundednessHelper(relatedTerms, indices, positions);
}

bool InductionPreprocessor::checkWellDefinedness(const vvector<Term*>& cases, vvector<vvector<TermList>>& missingCases)
{
  CALL("InductionPreprocessor::checkWellFoundedness");

  if (cases.empty()) {
    return false;
  }
  missingCases.clear();
  auto arity = cases[0]->arity();
  if (arity == 0) {
    return true;
  }
  vvector<vvector<TermStack>> availableTermsLists;
  availableTermsLists.emplace_back(arity);
  unsigned var = 0;
  for (unsigned i = 0; i < arity; i++) {
    availableTermsLists.back()[i].push(TermList(var++, false));
  }

  for (auto& c : cases) {
    vvector<vvector<TermStack>> nextAvailableTermsLists;
    for (unsigned i = 0; i < arity; i++) {
      auto arg = *c->nthArgument(i);
      // we check lazily for non-term algebra sort non-variables
      if (arg.isTerm() && env.signature->isTermAlgebraSort(SortHelper::getResultSort(arg.term()))) {
        auto tempLists = availableTermsLists;
        for (auto& availableTerms : tempLists) {
          TermAlgebra::excludeTermFromAvailables(availableTerms[i], arg, var);
        }
        nextAvailableTermsLists.insert(nextAvailableTermsLists.end(),
          tempLists.begin(), tempLists.end());
      } else {
        for (const auto& availableTerms : availableTermsLists) {
          if (!availableTerms[i].isEmpty()) {
            break;
          }
        }
      }
    }
    availableTermsLists = nextAvailableTermsLists;
  }

  for (const auto& availableTerms : availableTermsLists) {
    bool valid = true;
    vvector<vvector<TermList>> argTuples(1);
    for (const auto& v : availableTerms) {
      if (v.isEmpty()) {
        valid = false;
        break;
      }
      vvector<vvector<TermList>> temp;
      for (const auto& e : v) {
        for (auto a : argTuples) {
          a.push_back(e);
          temp.push_back(a);
        }
      }
      argTuples = temp;
    }
    if (valid) {
      missingCases.insert(missingCases.end(),
        argTuples.begin(), argTuples.end());
    }
  }
  return missingCases.empty();
}

} // Shell
