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
 * @file IndexManager.hpp
 * Defines class IndexManager
 *
 */

#ifndef __IndexManager__
#define __IndexManager__

#include "Forwards.hpp"
#include "Lib/DHMap.hpp"
#include "Index.hpp"
#include "Kernel/MismatchHandler.hpp"

#include "Lib/Allocator.hpp"


namespace Indexing
{

using namespace Lib;
using namespace Saturation;

enum IndexType {
  BINARY_RESOLUTION_SUBST_TREE=1,
  BACKWARD_SUBSUMPTION_SUBST_TREE,
  FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE,

  URR_UNIT_CLAUSE_SUBST_TREE,
  URR_NON_UNIT_CLAUSE_SUBST_TREE,
  
  SUPERPOSITION_SUBTERM_SUBST_TREE,
  SUPERPOSITION_LHS_SUBST_TREE,
  SUB_VAR_SUP_SUBTERM_SUBST_TREE,
  SUB_VAR_SUP_LHS_SUBST_TREE,

  DEMODULATION_SUBTERM_SUBST_TREE,
  DEMODULATION_LHS_CODE_TREE,
  DEMODULATION_LHS_SUBST_TREE,

  FW_SUBSUMPTION_CODE_TREE,
  FW_SUBSUMPTION_SUBST_TREE,
  BW_SUBSUMPTION_SUBST_TREE,

  FSD_SUBST_TREE,
  INTERMEDIATE_VALUE,
  REWRITE_RULE_SUBST_TREE,

  GLOBAL_SUBSUMPTION_INDEX,

  ACYCLICITY_INDEX,
  NARROWING_INDEX,
  PRIMITIVE_INSTANTIATION_INDEX,
  SKOLEMISING_FORMULA_INDEX,
  RENAMING_FORMULA_INDEX,

  UNIT_INT_COMPARISON_INDEX,
  INDUCTION_TERM_INDEX,
  STRUCT_INDUCTION_TERM_INDEX,
  // Rapid indexes
  MULTI_CLAUSE_NAT_IND_INDEX,
  RAPID_DENSITY_CLAUSE_INDEX,
  RAPID_ARRAY_INDEX,
  CHAIN_TERM_INDEX,
  CHAIN_BOUND_INDEX,
  INEQUALITY_RESOLUTION_UNIT_INDEX,
  INEQUALITY_RESOLUTION_NON_UNIT_INDEX,
  UNIT_INEQUALITY_LHS_INDEX,
  UNIT_INEQUALITY_RHS_INDEX,
  POINTER_CHAIN_LHS_INDEX,
  POINTER_CHAIN_RHS_INDEX  
};

class IndexManager
{
public:
  CLASS_NAME(IndexManager);
  USE_ALLOCATOR(IndexManager);

  /** alg can be zero, then it must be set by setSaturationAlgorithm */
  explicit IndexManager(SaturationAlgorithm* alg);
  ~IndexManager();

  void setSaturationAlgorithm(SaturationAlgorithm* alg) 
  { 
    CALL("IndexManager::setSaturationAlgorithm");
    ASS(!_alg);
    ASS(alg);
    _alg = alg; 
  }
  Index* request(IndexType t);
  void release(IndexType t);
  bool contains(IndexType t);
  Index* get(IndexType t);
  MismatchHandler* mismatchHandler(){ return _handler.isEmpty() ? nullptr : &_handler; }

  void provideIndex(IndexType t, Index* index);
private:

  struct Entry {
    Index* index;
    int refCnt;
  };
  SaturationAlgorithm* _alg;
  DHMap<IndexType,Entry> _store;

  MismatchHandler _handler;

  Index* create(IndexType t);
};

};

#endif /*__IndexManager__*/
