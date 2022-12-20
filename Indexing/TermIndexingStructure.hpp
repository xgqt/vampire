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
 * @file TermIndexingStructure.hpp
 * Defines class TermIndexingStructure.
 */


#ifndef __TermIndexingStructure__
#define __TermIndexingStructure__

#include "Index.hpp"
#include "Kernel/BottomUpEvaluation/TypedTermList.hpp"

namespace Indexing {

class TermIndexingStructure {
public:
  virtual ~TermIndexingStructure() {}

  virtual void insert(TermList t, Literal* lit, Clause* cls) = 0;
  virtual void remove(TermList t, Literal* lit, Clause* cls) = 0;
  virtual void insert(TermList t, TermList trm){ NOT_IMPLEMENTED; }
  virtual void insert(TermList t, TermList trm, Literal* lit, Clause* cls){ NOT_IMPLEMENTED; }

  virtual TermQueryResultIterator getUnifications(TermList t, bool retrieveSubstitutions = true, bool withConstraints = false) { NOT_IMPLEMENTED; }
  virtual TermQueryResultIterator getUnificationsUsingSorts(TypedTermList tt, bool retrieveSubstitutions = true, bool withConstraints = false) { NOT_IMPLEMENTED; }  
  virtual TermQueryResultIterator getGeneralizations(TermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual TermQueryResultIterator getInstances(TermList t, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }

  virtual bool generalizationExists(TermList t) { NOT_IMPLEMENTED; }

#if VDEBUG
  virtual void markTagged() = 0;
  virtual void output(std::ostream& output) const = 0;
#endif
  friend std::ostream& operator<<(std::ostream& out, TermIndexingStructure const& self)
  { self.output(out); return out; }
};


};

#endif /* __TermIndexingStructure__ */
