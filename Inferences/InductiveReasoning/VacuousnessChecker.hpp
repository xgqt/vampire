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
 * @file VacuousnessChecker.hpp
 * Defines class VacuousnessChecker
 *
 */

#ifndef __VacuousnessChecker__
#define __VacuousnessChecker__

#include <cmath>

#include "Forwards.hpp"

#include "Indexing/InductionFormulaIndex.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"

using namespace Indexing;

namespace Inferences
{

struct InductionContext;
class InductionClauseIterator;

namespace InductiveReasoning
{

class VacuousnessChecker
{
public:
  bool isVacuous(const InductionContext& ctx, InductionFormulaIndex::Entry* e);

private:
  bool isVacuous(Literal* lit, Term* t);
};

}

}

#endif /*__VacuousnessChecker__*/
