/**
 * @file Theory.hpp
 * Defines class Theory.
 */

#ifndef __Theory__
#define __Theory__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Exception.hpp"

#include "Sorts.hpp"
#include "Term.hpp"

namespace Kernel {

/**
 * Exception to be thrown when the requested operation cannot be performed,
 * e.g. because of overflow of a native type.
 */
class ArithmeticException : public ThrowableBase {};

class IntegerConstantType
{
public:
  static unsigned getSort() { return Sorts::SRT_INTEGER; }


  typedef int InnerType;

  IntegerConstantType() {}
  IntegerConstantType(InnerType v) : _val(v) {}
  explicit IntegerConstantType(const string& str);

  IntegerConstantType operator+(const IntegerConstantType& num) const;
  IntegerConstantType operator-(const IntegerConstantType& num) const;
  IntegerConstantType operator-() const;
  IntegerConstantType operator*(const IntegerConstantType& num) const;
  IntegerConstantType operator/(const IntegerConstantType& num) const;
  IntegerConstantType operator%(const IntegerConstantType& num) const;

  bool operator==(const IntegerConstantType& num) const;
  bool operator>(const IntegerConstantType& num) const;

  bool operator!=(const IntegerConstantType& num) const { return !((*this)==num); }
  bool operator<(const IntegerConstantType& o) const { return o>(*this); }
  bool operator>=(const IntegerConstantType& o) const { return !(o>(*this)); }
  bool operator<=(const IntegerConstantType& o) const { return !((*this)>o); }

  int toInt() const { return _val; }

  static IntegerConstantType floor(RationalConstantType rat);

  static Comparison comparePrecedence(IntegerConstantType n1, IntegerConstantType n2);

  string toString() const;
private:
  InnerType _val;
};

inline
std::ostream& operator<< (ostream& out, const IntegerConstantType& val) {
  return out << val.toInt();
}



/**
 * A class for representing rational numbers
 *
 * The class uses IntegerConstantType to store the numerator and denominator.
 * This ensures that if there is an overflow in the operations, an exception
 * will be raised by the IntegerConstantType methods.
 */
struct RationalConstantType {
  typedef IntegerConstantType InnerType;

  static unsigned getSort() { return Sorts::SRT_RATIONAL; }

  RationalConstantType() {}

  RationalConstantType(InnerType num, InnerType den);
  RationalConstantType(const string& num, const string& den);

  RationalConstantType operator+(const RationalConstantType& num) const;
  RationalConstantType operator-(const RationalConstantType& num) const;
  RationalConstantType operator-() const;
  RationalConstantType operator*(const RationalConstantType& num) const;
  RationalConstantType operator/(const RationalConstantType& num) const;

  bool isInt() const;

  bool operator==(const RationalConstantType& num) const;
  bool operator>(const RationalConstantType& num) const;

  bool operator!=(const RationalConstantType& num) const { return !((*this)==num); }
  bool operator<(const RationalConstantType& o) const { return o>(*this); }
  bool operator>=(const RationalConstantType& o) const { return !(o>(*this)); }
  bool operator<=(const RationalConstantType& o) const { return !((*this)>o); }


  string toString() const;

  const InnerType& numerator() const { return _num; }
  const InnerType& denominator() const { return _den; }

  static Comparison comparePrecedence(RationalConstantType n1, RationalConstantType n2);

protected:
  void init(InnerType num, InnerType den);

private:
  void cannonize();

  InnerType _num;
  InnerType _den;
};

inline
std::ostream& operator<< (ostream& out, const RationalConstantType& val) {
  return out << val.toString();
}


class RealConstantType : public RationalConstantType
{
public:
  static unsigned getSort() { return Sorts::SRT_REAL; }

  RealConstantType() {}
  explicit RealConstantType(const string& number);
  explicit RealConstantType(const RationalConstantType& rat) : RationalConstantType(rat) {}

  RealConstantType operator+(const RealConstantType& num) const
  { return RealConstantType(RationalConstantType::operator+(num)); }
  RealConstantType operator-(const RealConstantType& num) const
  { return RealConstantType(RationalConstantType::operator-(num)); }
  RealConstantType operator-() const
  { return RealConstantType(RationalConstantType::operator-()); }
  RealConstantType operator*(const RealConstantType& num) const
  { return RealConstantType(RationalConstantType::operator*(num)); }
  RealConstantType operator/(const RealConstantType& num) const
  { return RealConstantType(RationalConstantType::operator/(num)); }

  string toNiceString() const;

  static Comparison comparePrecedence(RealConstantType n1, RealConstantType n2);
private:
  static bool parseDouble(const string& num, RationalConstantType& res);

};

inline
std::ostream& operator<< (ostream& out, const RealConstantType& val) {
  return out << val.toString();
}


/**
 * A singleton class handling tasks related to theory symbols in Vampire
 */
class Theory
{
public:
  /**
   * Interpreted symbols and predicates
   *
   * If interpreted_evaluation is enabled, predicates GREATER_EQUAL,
   * LESS and LESS_EQUAL should not appear in the run of the
   * SaturationAlgorithm (they'll be immediately simplified by the
   * InterpretedEvaluation simplification).
   */
  enum Interpretation
  {
    //predicates

    EQUAL,

    INT_IS_INT,
    INT_IS_RAT,
    INT_IS_REAL,
    INT_GREATER,
    INT_GREATER_EQUAL,
    INT_LESS,
    INT_LESS_EQUAL,
    INT_DIVIDES,

    RAT_IS_INT,
    RAT_IS_RAT,
    RAT_IS_REAL,
    RAT_GREATER,
    RAT_GREATER_EQUAL,
    RAT_LESS,
    RAT_LESS_EQUAL,
    RAT_DIVIDES,

    REAL_IS_INT,
    REAL_IS_RAT,
    REAL_IS_REAL,
    REAL_GREATER,
    REAL_GREATER_EQUAL,
    REAL_LESS,
    REAL_LESS_EQUAL,
    REAL_DIVIDES,


    //numeric functions

    INT_SUCCESSOR,
    INT_UNARY_MINUS,
    INT_PLUS,
    INT_MINUS,
    INT_MULTIPLY,
    INT_DIVIDE,
    INT_MODULO,

    RAT_UNARY_MINUS,
    RAT_PLUS,
    RAT_MINUS,
    RAT_MULTIPLY,
    RAT_DIVIDE,

    REAL_UNARY_MINUS,
    REAL_PLUS,
    REAL_MINUS,
    REAL_MULTIPLY,
    REAL_DIVIDE,


    //conversion functions
    INT_TO_INT,
    INT_TO_RAT,
    INT_TO_REAL,
    RAT_TO_INT,
    RAT_TO_RAT,
    RAT_TO_REAL,
    REAL_TO_INT,
    REAL_TO_RAT,
    REAL_TO_REAL,
    
    //array functions for array1 of INT->INT
    SELECT1_INT,
    STORE1_INT,
      
    //array functions for array2 of INT->INT
    SELECT2_INT,
    STORE2_INT, 

    /**
     * Maximal element number in the enum Interpretation
     *
     * At some points we make use of the fact that we can iterate through all
     * interpretations by going through the set {0,...,MAX_INTERPRETED_ELEMENT}.
     */
    MAX_INTERPRETED_ELEMENT = STORE2_INT,
    INVALID_INTERPRETATION
  };
  static unsigned getArity(Interpretation i);
  static bool isFunction(Interpretation i);
  static bool isInequality(Interpretation i);
  static BaseType* getOperationType(Interpretation i);
  static bool hasSingleSort(Interpretation i);
  static unsigned getOperationSort(Interpretation i);
  static bool isConversionOperation(Interpretation i);
    
  static FunctionType* getArrayOperationType(Interpretation i);

  static bool isArrayOperation(Interpretation i);
  static unsigned getArrayOperationSort(Interpretation i);
  static unsigned  getArrayDomainSort(Interpretation i);

  unsigned getArrayExtSkolemFunction(unsigned i);
    
  static Theory* instance();

  bool isInterpretedConstant(unsigned func);
  bool isInterpretedConstant(Term* t);
  bool isInterpretedConstant(TermList t);

  bool isInterpretedPredicate(unsigned pred);
  bool isInterpretedPredicate(Literal* lit);
  bool isInterpretedPredicate(Literal* lit, Interpretation itp);

  bool isInterpretedFunction(unsigned func);
  bool isInterpretedFunction(Term* t);
  bool isInterpretedFunction(TermList t);
  bool isInterpretedFunction(Term* t, Interpretation itp);
  bool isInterpretedFunction(TermList t, Interpretation itp);

  Interpretation interpretFunction(unsigned func);
  Interpretation interpretFunction(Term* t);
  Interpretation interpretFunction(TermList t);
  Interpretation interpretPredicate(unsigned pred);
  Interpretation interpretPredicate(Literal* t);

  unsigned getFnNum(Interpretation itp);
  unsigned getPredNum(Interpretation itp);

  Term* fun1(Interpretation itp, TermList arg);
  Term* fun2(Interpretation itp, TermList arg1, TermList arg2);
  Term* fun3(Interpretation itp, TermList arg1, TermList arg2, TermList arg3);
  Literal* pred2(Interpretation itp, bool polarity, TermList arg1, TermList arg2);

  /**
   * Try to interpret the term list as an integer constant. If it is an
   * integer constant, return true and save the constant in @c res, otherwise
   * return false.
   */
  bool tryInterpretConstant(TermList trm, IntegerConstantType& res)
  {
    CALL("Theory::tryInterpretConstant(TermList,IntegerConstantType)");
    if (!trm.isTerm()) {
      return false;
    }
    return tryInterpretConstant(trm.term(),res);
  }
  bool tryInterpretConstant(const Term* t, IntegerConstantType& res);
  /**
   * Try to interpret the term list as an rational constant. If it is an
   * rational constant, return true and save the constant in @c res, otherwise
   * return false.
   */
  bool tryInterpretConstant(TermList trm, RationalConstantType& res)
  {
    CALL("Theory::tryInterpretConstant(TermList,RationalConstantType)");
    if (!trm.isTerm()) {
      return false;
    }
    return tryInterpretConstant(trm.term(),res);
  }
  bool tryInterpretConstant(const Term* t, RationalConstantType& res);
  /**
   * Try to interpret the term list as an real constant. If it is an
   * real constant, return true and save the constant in @c res, otherwise
   * return false.
   */
  bool tryInterpretConstant(TermList trm, RealConstantType& res)
  {
    CALL("Theory::tryInterpretConstant(TermList,RealConstantType)");
    if (!trm.isTerm()) {
      return false;
    }
    return tryInterpretConstant(trm.term(),res);
  }
  bool tryInterpretConstant(const Term* t, RealConstantType& res);

  Term* representConstant(const IntegerConstantType& num);
  Term* representConstant(const RationalConstantType& num);
  Term* representConstant(const RealConstantType& num);

  Term* representIntegerConstant(string str);
  Term* representRealConstant(string str);
private:
  Theory();
  static FunctionType* getConversionOperationType(Interpretation i);
  unsigned _array1SkolemFunction;
  unsigned _array2SkolemFunction;
};

typedef Theory::Interpretation Interpretation;

/**
 * Pointer to the singleton Theory instance
 */
extern Theory* theory;
}

#endif // __Theory__
