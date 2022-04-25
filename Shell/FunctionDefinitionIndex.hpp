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
 * @file FunctionDefinitionIndex.hpp
 * Defines helper classes for induction templates and preprocessing
 */

#ifndef __FunctionDefinitionIndex__
#define __FunctionDefinitionIndex__

#include "Forwards.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Kernel/Problem.hpp"
#include "Lib/STL.hpp"

namespace Shell {

using namespace Indexing;
using namespace Kernel;
using namespace Lib;

struct Branch {
  TermList header;
  TermList body;
  LiteralStack literals;
};

class FunctionDefinitionIndex
{
public:
  static void preprocess(Problem& prb);

  static TermQueryResultIterator getGeneralizations(TermList t) {
    return _tis.getGeneralizations(t, true);
  }

#if VDEBUG
  static void addTestClause(TermList t, Literal* lit, Clause* cl) {
    _tis.insert(t, lit, cl);
  }
#endif

private:
  static bool preprocess(Formula* f, Unit* unit);

  static TermSubstitutionTree _tis;
};

} // Shell

#endif
