/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "FunctionDefinitionIndex.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Lib/SharedSet.hpp"

using namespace Kernel;

namespace Shell {

TermSubstitutionTree FunctionDefinitionIndex::_tis;

void FunctionDefinitionIndex::preprocess(Problem& prb)
{
  CALL("FunctionDefinitionIndex::preprocess(Problem&)");
  UnitList::DelIterator it(prb.units());
  while (it.hasNext()) {
    auto u = it.next();
    if (u->isClause()) {
      continue;
    }
    auto f = static_cast<FormulaUnit*>(u)->formula();
    if (f->connective() == LITERAL && static_cast<AtomicFormula*>(f)->isFunctionDefinition()) {
      // if the definition could be processed, we remove the
      // unit, otherwise it will be dealt with normally
      if (preprocess(f, u)) {
        it.del();
      }
    }
  }
}

bool FunctionDefinitionIndex::preprocess(Formula* f, Unit* unit)
{
  CALL("FunctionDefinitionIndex::preprocess(Formula*)");
  ASS_EQ(f->connective(), LITERAL);

  auto l = f->literal();
  ASS(l->isEquality());
  
  TermList sort = SortHelper::getEqualityArgumentSort(l);
  Stack<Branch> todos;
  Stack<Branch> done;
  todos.push({
    .header = *l->nthArgument(0),
    .body = *l->nthArgument(1),
    .literals = LiteralStack()
  });
  while (todos.isNonEmpty()) {
    auto b = todos.pop();
    if (b.body.isVar() || !b.body.term()->isSpecial()) {
      done.push(std::move(b));
      continue;
    }
    auto t = b.body.term();
    Term::SpecialTermData *sd = t->getSpecialData();
    switch (sd->getType()) {
      case Term::SF_FORMULA:
      case Term::SF_ITE:
      case Term::SF_LET:
      case Term::SF_LET_TUPLE:
      case Term::SF_TUPLE: {
        return false;
      }

      // case Term::SF_FORMULA: {
      // }

      // case Term::SF_ITE: {
      //   sort = sd->getSort();
      //   conditions.push(sd->getCondition());
      //   thenBranches.push(*term->nthArgument(0));
      //   elseBranches.push(*term->nthArgument(1));
      //   break;
      // }

      // case Term::SF_LET:
      // case Term::SF_LET_TUPLE: {
      //   TermList contents = *term->nthArgument(0);
      //   TermList processedLet = eliminateLet(sd, contents);
      //   return findITEs(processedLet, variables, conditions, thenBranches,
      //     elseBranches, matchVariables, matchConditions, matchBranches);
      // }

      // case Term::SF_TUPLE: {
      //   TermList tupleTerm = TermList(sd->getTupleTerm());
      //   return findITEs(tupleTerm, variables, conditions, thenBranches,
      //                   elseBranches, matchVariables, matchConditions, matchBranches);
      // }

      case Term::SF_MATCH: {
        sort = sd->getSort();
        auto matched = *t->nthArgument(0);
        for (unsigned int i = 1; i < t->arity(); i += 2) {
          Branch bn = b;
          Substitution subst;
          subst.bind(matched.var(), *t->nthArgument(i));
          bn.body = SubstHelper::apply(*t->nthArgument(i + 1), subst);
          bn.header = SubstHelper::apply(b.header, subst);
          todos.push(bn);
        }
        break;
      }

      default:
        ASSERTION_VIOLATION_REP(t->toString());
    }
  }
  for (auto& b : done) {
    auto mainLit = Literal::createEquality(true, b.header, b.body, sort);
    b.literals.push(mainLit);
    auto rwCl = Clause::fromStack(b.literals, FormulaTransformation(InferenceRule::CLAUSIFY,unit));
    rwCl->setSplits(SplitSet::getEmpty());
    rwCl->setStore(Clause::ACTIVE);
    _tis.insert(b.header, mainLit, rwCl);
  }
  return true;
}

} // Shell
