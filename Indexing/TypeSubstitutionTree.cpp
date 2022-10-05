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
 * @file TypeSubstitutionTree.cpp
 * Implements class TypeSubstitutionTree.
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"
#include "Lib/SmartPtr.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Shell/Options.hpp"

#include "TypeSubstitutionTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

TypeSubstitutionTree::TypeSubstitutionTree(MismatchHandler* hndlr)
: SubstitutionTree(env.signature->typeCons()), _handler(hndlr)
{}

void TypeSubstitutionTree::insert(TermList sort, LeafData ld)
{
  CALL("TypeSubstitutionTree::insert");
  handleTerm(sort,ld,true);
}

void TypeSubstitutionTree::remove(TermList sort, LeafData ld)
{
  CALL("TypeSubstitutionTree::remove");
  handleTerm(sort,ld,false);
}

#define QRS_QUERY_BANK 0
#define QRS_RESULT_BANK 1

struct TypeSubstitutionTree::ToTermUnifier
{
  ToTermUnifier(TermList queryTerm, TermList sort, bool retrieveSubstitutions, MismatchHandler* hndlr)
  : _queryTerm(queryTerm), _sort(sort), _retrieveSubstitutions(retrieveSubstitutions), _handler(hndlr) {}

  bool enter (const TermQueryResult& tqr) {
    CALL("TypeSubstitutionTree::ToTermUnifier::enter");
    if(_retrieveSubstitutions){
      RobSubstitution* subst=tqr.substitution->tryGetRobSubstitution();
      ASS(subst);
      // instantiate the sort
      TermList sortI = subst->apply(_sort,QRS_QUERY_BANK);
     
      if(_queryTerm.isVar() || tqr.term.isVar()){
        // If one of the terms is a variable, we extend the sort unifier to 
        // a term unifier if this isn't going to take place in the standard tree
        ASS(_handler)
        if(_handler->isConstraintTerm(tqr.term, sortI).maybe()){
          // term is also in the standard tree and we will unify with it there
          return false;
        }
        
        subst->bdRecord(_bdata);
        ALWAYS(subst->unify(_queryTerm, QRS_QUERY_BANK, tqr.term, QRS_RESULT_BANK));
        subst->bdDone();        
      } else{
        return subst->tryAddConstraint(_queryTerm, QRS_QUERY_BANK, tqr.term, QRS_RESULT_BANK, sortI, _bdata);
      }
    }
    return true;
  }

  void leave(const TermQueryResult& tqr) {
    CALL("TypeSubstitutionTree::ToTermUnifier::leave");

    if(_retrieveSubstitutions){
       _bdata.backtrack();
      ASS(_bdata.isEmpty());
    }
  }

private:
  TermList _queryTerm;
  TermList _sort;
  bool _retrieveSubstitutions;
  MismatchHandler* _handler;
  BacktrackData _bdata;
};

/**
 * According to value of @b insert, insert or remove leaf data.
 */
void TypeSubstitutionTree::handleTerm(TermList sort, LeafData ld, bool insert)
{
  CALL("TypeSubstitutionTree::handleTerm");

  ASS(sort.isVar() || sort.term()->isSort());

  if(sort.isOrdinaryVar()) {
    if(insert) {
      _vars.insert(ld);
    } else {
      // why is this case needed?
      _vars.remove(ld);
    }
  }  else {
    ASS(sort.isTerm());
    Term* term=sort.term();

    Renaming normalizer;
    normalizer.normalizeVariables(ld.term);

    Term* normSort=normalizer.apply(term);

    BindingMap svBindings;
    getBindings(normSort, svBindings);

    unsigned rootNodeIndex=getRootNodeIndex(normSort);

    if(insert) {
      SubstitutionTree::insert(&_nodes[rootNodeIndex], svBindings, ld);
    } else {
      SubstitutionTree::remove(&_nodes[rootNodeIndex], svBindings, ld);
    }
  }
}

TermQueryResultIterator TypeSubstitutionTree::getUnifications(TermList sort, TermList trm,
	  bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::getUnifications");
 
  if(sort.isOrdinaryVar()) {
    return pvi(getContextualIterator(getAllUnifyingIterator(sort,retrieveSubstitutions), 
      ToTermUnifier(trm, sort, retrieveSubstitutions, _handler)));
  } else {
    ASS(sort.isTerm());
    auto it1 = 
      pvi(getContextualIterator(ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), sort, retrieveSubstitutions), 
        ToTermUnifier(trm, sort, retrieveSubstitutions, _handler)));
    auto it2 = getContextualIterator(
	    getResultIterator<UnificationsIterator>(sort.term(), retrieveSubstitutions), 
        ToTermUnifier(trm, sort, retrieveSubstitutions, _handler));
    return pvi(getConcatenatedIterator(it1, it2));     
  }
}

/**
 * Functor, that transforms &b QueryResult struct into
 * @b TermQueryResult.
 */
struct TypeSubstitutionTree::TermQueryResultFn
{
  TermQueryResult operator() (const QueryResult& qr) {
    return TermQueryResult(qr.first->term, qr.first->literal,
	    qr.first->clause, qr.second);
  }
};

template<class Iterator>
TermQueryResultIterator TypeSubstitutionTree::getResultIterator(Term* trm,
	  bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::getResultIterator");

  //cout << "getResultIterator " << trm->toString() << endl;

  TermQueryResultIterator result = TermQueryResultIterator::getEmpty();
  
  Node* root = _nodes[getRootNodeIndex(trm)];

  if(root){
    if(root->isLeaf()) {
      LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
      result = ldIteratorToTQRIterator(ldit,TermList(trm),retrieveSubstitutions);
    }
    else{
      VirtualIterator<QueryResult> qrit=vi( new Iterator(this, root, trm, retrieveSubstitutions,false,false,_handler) );
      result = pvi( getMappingIterator(qrit, TermQueryResultFn()) );
    }
  }

  return result;
}

struct TypeSubstitutionTree::LDToTermQueryResultFn
{
  TermQueryResult operator() (const LeafData& ld) {
    return TermQueryResult(ld.term, ld.literal, ld.clause);
  }
};

struct TypeSubstitutionTree::LDToTermQueryResultWithSubstFn
{
  LDToTermQueryResultWithSubstFn(MismatchHandler* hndlr)
  {
    _subst=RobSubstitutionSP(new RobSubstitution(hndlr));
  }
  TermQueryResult operator() (const LeafData& ld) {
    return TermQueryResult(ld.term, ld.literal, ld.clause,
    ResultSubstitution::fromSubstitution(_subst.ptr(),
	    QRS_QUERY_BANK,QRS_RESULT_BANK));
  }
private:
  RobSubstitutionSP _subst;
};

struct TypeSubstitutionTree::LeafToLDIteratorFn
{
  LDIterator operator() (Leaf* l) {
    CALL("TypeSubstitutionTree::LeafToLDIteratorFn()");
    return l->allChildren();
  }
};

struct TypeSubstitutionTree::UnifyingContext
{
  UnifyingContext(TermList querySort)
  : _querySort(querySort) {}
  bool enter(TermQueryResult qr)
  {
    CALL("TypeSubstitutionTree::UnifyingContext::enter");
    //TODO unnecessary work here. We had the sort and then lost it
    TermList qrSort = SortHelper::getTermSort(qr.term, qr.literal);

    ASS(qr.substitution);
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    bool unified = subst->unify(_querySort, QRS_QUERY_BANK, qrSort, QRS_RESULT_BANK);
    return unified;
  }
  void leave(TermQueryResult qr)
  {
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    subst->reset();
  }
private:
  TermList _querySort;
};

template<class LDIt>
TermQueryResultIterator TypeSubstitutionTree::ldIteratorToTQRIterator(LDIt ldIt,
	TermList querySort, bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::ldIteratorToTQRIterator");
  // only call withConstraints if we are also getting substitions, the other branch doesn't handle constraints
  //ASS(retrieveSubstitutions); 
 
  if(retrieveSubstitutions) {
    return pvi( getContextualIterator(
	    getMappingIterator(
		    ldIt,
		    LDToTermQueryResultWithSubstFn(_handler)),
	    UnifyingContext(querySort)) );
  } else {
    return pvi( getMappingIterator(
	    ldIt,
	    LDToTermQueryResultFn()) );
  }
}

TermQueryResultIterator TypeSubstitutionTree::getAllUnifyingIterator(TermList sort,
	  bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::getAllUnifyingIterator");

  ASS(sort.isVar());

  auto it1 = getFlattenedIterator(getMappingIterator(vi( new LeafIterator(this) ), LeafToLDIteratorFn()));

  return ldIteratorToTQRIterator(
    getConcatenatedIterator(it1,LDSkipList::RefIterator(_vars)),
    sort, retrieveSubstitutions);
  
}




}
