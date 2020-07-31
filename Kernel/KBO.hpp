
/*
 * File KBO.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file KBO.hpp
 * Defines class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#ifndef __KBO__
#define __KBO__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"

#include "Ordering.hpp"

#define SPECIAL_WEIGHT_FILENAME_RANDOM      "random"
#define SPECIAL_WEIGHT_IDENT_VAR            "$var"
#define SPECIAL_WEIGHT_IDENT_INTRODUCED     "$introduced"
#define SPECIAL_WEIGHT_IDENT_DEFAULT_WEIGHT "$default"
#define SPECIAL_WEIGHT_IDENT_NUM_INT        "$int"
#define SPECIAL_WEIGHT_IDENT_NUM_RAT        "$rat"
#define SPECIAL_WEIGHT_IDENT_NUM_REAL       "$real"

namespace Kernel {

using namespace Lib;

struct PredSigTraits;
struct FuncSigTraits;

/**
 * Class for instances of the Knuth-Bendix orderings
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBO
: public PrecedenceOrdering
{
public:
  CLASS_NAME(KBO);
  USE_ALLOCATOR(KBO);

  using Weight = unsigned;

  /** 
   * Contains special weights for, variables and interpreted functions for SigTraits == FuncSigTraits, 
   * and nothing for SigTraits == PredSigTraits 
   */
  template<class SigTraits>
  struct SpecialWeights;

  template<>
  struct SpecialWeights<PredSigTraits> 
  { 
    inline bool tryAssign(const vstring& name, unsigned weight) 
    { return false; }

    inline static SpecialWeights dflt() 
    { return { }; }

    bool tryGetWeight(unsigned functor, unsigned& weight) const;
  };

  template<>
  struct SpecialWeights<FuncSigTraits> 
  {
    Weight _variableWeight;
    Weight _numInt;
    Weight _numRat;
    Weight _numReal;
    inline bool tryAssign(const vstring& name, unsigned weight) 
    {
      if (name == SPECIAL_WEIGHT_IDENT_VAR     ) { _variableWeight = weight; return true; } 
      if (name == SPECIAL_WEIGHT_IDENT_NUM_INT ) { _numInt  = weight; return true; } 
      if (name == SPECIAL_WEIGHT_IDENT_NUM_REAL) { _numReal = weight; return true; } 
      if (name == SPECIAL_WEIGHT_IDENT_NUM_RAT ) { _numRat  = weight; return true; } 
      return false;
    }

    inline static SpecialWeights dflt() 
    { 
      return { 
        ._variableWeight = 1, 
        ._numInt  = 1,
        ._numRat  = 1,
        ._numReal = 1,
      }; 
    }

    bool tryGetWeight(unsigned functor, unsigned& weight) const;
  };


  template<class SigTraits>
  struct WeightMap {
    friend class KBO;
    DArray<Weight> _weights;

    /** Weight of function symbols not occurring in the signature, i.e. that are introduced during proof search */
    Weight _introducedSymbolWeight;

    /** Special weights that are only present for function/predicate symbols. */
    SpecialWeights<SigTraits> _specialWeights;

    Weight symbolWeight(Term*    t      ) const;
    Weight symbolWeight(unsigned functor) const;

                           static WeightMap dflt();
  private:
    template<class Random> static WeightMap randomized(unsigned maxWeight, Random random);
  };

  KBO(Problem& prb, const Options& opt);
  KBO(
      // KBO params
      WeightMap<FuncSigTraits> funcWeights, 
      WeightMap<PredSigTraits> predWeights, 

      // precedence ordering params
      DArray<int> funcPrec, 
      DArray<int> predPrec, 
      DArray<int> predLevels,

      // other
      bool reverseLCM);

  virtual ~KBO();
  void showConcrete(ostream&) const override;
  void checkAdmissibility() const;

  using PrecedenceOrdering::compare;
  Result compare(TermList tl1, TermList tl2) const override;
protected:
  Result comparePredicates(Literal* l1, Literal* l2) const override;


  class State;

  // int functionSymbolWeight(unsigned fun) const;
  int symbolWeight(Term* t) const;

private:

  WeightMap<FuncSigTraits> _funcWeights;
  WeightMap<PredSigTraits> _predWeights;

  template<class SigTraits> const WeightMap<SigTraits>& getWeightMap() const;
  template<class SigTraits> WeightMap<SigTraits> weightsFromOpts(const Options& opts) const;
  template<class SigTraits> WeightMap<SigTraits> weightsFromFile(const Options& opts) const;

  template<class SigTraits> 
  void showConcrete_(ostream&) const;

  /**
   * State used for comparing terms and literals
   */
  mutable State* _state;
};

}
#endif
