/**
 * @file Term.hpp
 * Defines class Term (also serving as term arguments)
 *
 * @since 18/04/2006 Bellevue
 * @since 06/05/2007 Manchester, changed into a single class instead of three
 */

#ifndef __Term__
#define __Term__

#include <cstdlib>
#include <string>
#include <iosfwd>
#include <utility>

#include "../Forwards.hpp"
#include "../Debug/Assertion.hpp"
#include "../Debug/Tracer.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/Portability.hpp"
#include "../Lib/XML.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/Metaiterators.hpp"

#include "MatchTag.hpp"


#define TERM_DIST_VAR_UNKNOWN 0x7FFFFF

namespace Kernel {

using namespace std;
using namespace Lib;

/** Tag denoting the kind of this term
 * @since 19/02/2008 Manchester, moved outside of the Term class
 */
enum TermTag {
  /** reference to another term */
  REF = 0u,
  /** ordinary variable */
  ORD_VAR = 1u,
  /** (function) symbol */
  FUN = 2u,
  /** special variable */
  SPEC_VAR = 3u,
};

/**
 * Class containing either a pointer to a compound term or
 * a variable number or a functor.
 */
class TermList {
public:
  TermList() {}
  explicit TermList(size_t data) : _content(data) {}
  explicit TermList(Term* t) : _term(t) {}
  TermList(unsigned var, bool special)
  {
    if(special) {
      makeSpecialVar(var);
    } else {
      makeVar(var);
    }
  }

  /** the tag */
  inline TermTag tag() const { return (TermTag)(_content & 0x0003); }
  /** the term list is empty */
  inline bool isEmpty() const
  { return tag() == FUN; }
  /** the term list is non-empty */
  inline bool isNonEmpty() const
  { return tag() != FUN; }
  /** next term in this list */
  inline TermList* next()
  { return this-1; }
  /** next term in this list */
  inline const TermList* next() const
  { return this-1; }
  /** the term contains a variable as its head */
  inline bool isVar() const { return (_content & 0x0001) == 1; }
  /** the term contains an ordinary variable as its head */
  inline bool isOrdinaryVar() const { return tag() == ORD_VAR; }
  /** the term contains a special variable as its head */
  inline bool isSpecialVar() const { return tag() == SPEC_VAR; }
  /** return the variable number */
  inline unsigned var() const
  { ASS(isVar()); return _content / 4; }
  /** the term contains reference to Term class */
  inline bool isTerm() const
  { return tag() == REF; }
  inline const Term* term() const
  { return _term; }
  inline Term* term()
  { return _term; }
  /** True of the terms have the same content. Useful for comparing
   * arguments of shared terms. */
  inline bool sameContent(const TermList* t) const
  { return _content == t->_content ; }
  /** return the content, useful for e.g., term argument comparison */
  inline size_t content() const { return _content; }
  string toString() const;
  /** make the term into an ordinary variable with a given number */
  inline void makeVar(unsigned vnumber)
  { _content = vnumber * 4 + ORD_VAR; }
  /** make the term into a special variable with a given number */
  inline void makeSpecialVar(unsigned vnumber)
  { _content = vnumber * 4 + SPEC_VAR; }
  /** make the term empty (so that isEmpty() returns true) */
  inline void makeEmpty()
  { _content = FUN; }
  /** make the term into a reference */
  inline void setTerm(Term* t)
  { _term = t; }
  static void argsToString(Stack<const TermList*>&,string& str);
  static bool sameTop(TermList ss, TermList tt);
  static bool sameTopFunctor(TermList ss, TermList tt);
  static bool equals(TermList t1, TermList t2);
  bool containsSubterm(TermList v);
  bool containsAllVariablesOf(TermList t);

#if VDEBUG
  void assertValid() const;
#endif

  inline bool operator==(const TermList& t) const
  { return _content==t._content; }
  inline bool operator!=(const TermList& t) const
  { return _content!=t._content; }
  inline bool operator<(const TermList& t) const
  { return _content<t._content; }
  inline bool operator>(const TermList& t) const
  { return _content>t._content; }

private:
  union {
    /** reference to another term */
    Term* _term;
    /** raw content, can be anything */
    size_t _content;
    /** Used by Term, storing some information about the term using bits */
    struct {
      /** tag, always FUN */
      unsigned tag : 2;
      /** polarity, used only for literals */
      unsigned polarity : 1;
      /** true if commutative/symmetric */
      unsigned commutative : 1;
      /** true if shared */
      unsigned shared : 1;
      /** true if literal */
      unsigned literal : 1;
      /** Ordering comparison result for commutative term arguments, one of
       * 0 (unknown) 1 (less), 2 (equal), 3 (greater), 4 (incomparable)
       * @see Term::ArgumentOrder */
      unsigned order : 3;
      /** Number of distincs variables in the term, equal
       * to TERM_DIST_VAR_UNKNOWN if the number has not been
       * computed yet. */
      unsigned distinctVars : 23;
      /** reserved for whatever */
#if ARCH_X64
# if USE_MATCH_TAG
      MatchTag matchTag; //32 bits
# else
      unsigned reserved : 32;
# endif
#else
//      unsigned reserved : 0;
#endif
    } _info;
  };
  friend class Indexing::TermSharing;
  friend class Term;
  friend class Literal;
}; // class TermList

ASS_STATIC(sizeof(TermList)==sizeof(size_t));

/**
 * Class to represent terms and lists of terms.
 * @since 19/02/2008 Manchester, changed to use class TermList
 */
class Term
{
public:
  Term() throw();
  explicit Term(const Term& t) throw();
  void orderArguments();
  static Term* create(unsigned function, unsigned arity, TermList* args);
  static Term* create(Term* t,TermList* args);
  static Term* createNonShared(Term* t,TermList* args);
  static Term* createNonShared(Term* t);
  static Term* cloneNonShared(Term* t);
  /** Function or predicate symbol of a term */
  const unsigned functor() const
  {
    return _functor;
  }

  static XMLElement variableToXML(unsigned var);
  string toString() const;
  static string variableToString(unsigned var);
  static string variableToString(TermList var);
  /** return the arguments */
  const TermList* args() const
  { return _args + _arity; }
  /** return the nth argument (counting from 0) */
  const TermList* nthArgument(int n) const
  {
    ASS(n >= 0);
    ASS((unsigned)n < _arity);

    return _args + (_arity - n);
  }
  /** return the nth argument (counting from 0) */
  TermList* nthArgument(int n)
  {
    ASS(n >= 0);
    ASS((unsigned)n < _arity);

    return _args + (_arity - n);
  }
  /** return the arguments */
  TermList* args()
  { return _args + _arity; }
  unsigned hash() const;
  /** return the arity */
  unsigned arity() const
  { return _arity; }
  static void* operator new(size_t,unsigned arity);
  /** make the term into a symbol term */
  void makeSymbol(unsigned number,unsigned arity)
  {
    _functor = number;
    _arity = arity;
  }
  void destroy();
  void destroyNonShared();
  Term* apply(Substitution& subst);

  /** True if the term is ground. Only applicable to shared terms */
  bool ground() const
  {
    ASS(_args[0]._info.shared);
    return ! _vars;
  } // ground

  /** True if the term is shared */
  bool shared() const
  { return _args[0]._info.shared; } // shared

  /**
   * True if the term's function/predicate symbol is commutative/symmetric.
   * @pre the term must be complex
   */
  bool commutative() const
  {
    return _args[0]._info.commutative;
  } // commutative

  /** Return the weight. Applicable only to shared terms */
  unsigned weight() const
  {
    ASS(shared());
    return _weight;
  }

  /** Mark term as shared */
  void markShared()
  {
    ASS(! shared());
    _args[0]._info.shared = 1u;
  } // markShared

  /** Set term weight */
  void setWeight(unsigned w)
  {
    _weight = w;
  } // setWeight

  /** Set the number of variables */
  void setVars(unsigned v)
  {
    _vars = v;
  } // setVars

  /** Return the number of variables */
  unsigned vars() const
  {
    ASS(_args[0]._info.shared);
    return _vars;
  } // vars()

  const string& functionName() const;

  /** True if the term is, in fact, a literal */
  bool isLiteral() const { return _args[0]._info.literal; }

  /** Return an index of the argument to which @b arg points */
  unsigned getArgumentIndex(TermList* arg)
  {
    CALL("Term::getArgumentIndex");

    unsigned res=arity()-(arg-_args);
    ASS_L(res,arity());
    return res;
  }

#if VDEBUG
  string headerToString() const;
  void assertValid() const;
#endif


  /**
   * Iterator that yields variables of specified
   * @b term in DFS left to right order.
   */
  class VariableIterator
  : public IteratorCore<TermList>
  {
  public:
    DECL_ELEMENT_TYPE(TermList);
    VariableIterator(const Term* term) : _stack(8), _used(false)
    {
      if(!term->shared() || !term->ground()) {
	_stack.push(term->args());
      }
    }

    bool hasNext();
    /** Return the next variable
     * @warning hasNext() must have been called before */
    TermList next()
    {
      ASS(!_used);
      ASS(_stack.top()->isVar());
      _used=true;
      return *_stack.top();
    }
  private:
    Stack<const TermList*> _stack;
    bool _used;
  };

  static TermIterator getVariableIterator(TermList tl)
  {
    if(tl.isVar()) {
      return pvi( getSingletonIterator(tl) );
    }
    ASS(tl.isTerm());
    return vi( new VariableIterator(tl.term()) );
  }

  /**
   * Iterator that yields proper subterms
   * of specified @b term in DFS left to right order.
   */
  class SubtermIterator
  : public IteratorCore<TermList>
  {
  public:
    SubtermIterator(const Term* term) : _stack(8), _used(false)
    {
      pushNext(term->args());
    }

    bool hasNext();
    /** Return next subterm
     * @warning hasNext() must have been called before */
    TermList next()
    {
      ASS(!_used && !_stack.isEmpty());
      _used=true;
      return *_stack.top();
    }
  private:
    inline
    void pushNext(const TermList* t)
    {
      if(!t->isEmpty()) {
	_stack.push(t);
      }
    }
    Stack<const TermList*> _stack;
    bool _used;
  };

  /**
   * Iterator that yields proper subterms
   * of specified @b term for a function first yielding
   * its params left to right and then the function itself.
   */
  class PolishSubtermIterator
  : public IteratorCore<TermList>
  {
  public:
    PolishSubtermIterator(const Term* term) : _stack(8), _used(false)
    {
      pushNext(term->args());
    }

    bool hasNext();
    /** Return next subterm
     * @warning hasNext() must have been called before */
    TermList next()
    {
      ASS(!_used && !_stack.isEmpty());
      _used=true;
      return *_stack.top();
    }
  private:
    inline
    void pushNext(const TermList* t)
    {
      while(!t->isEmpty()) {
	_stack.push(t);
	if(!t->isTerm()) {
	  return;
	}
	t=t->term()->args();
      }
    }
    Stack<const TermList*> _stack;
    bool _used;
  };

  /**
   * Iterator that yields non-variable proper subterms
   * of specified @b term in DFS left to right order.
   */
  class NonVariableIterator
  : public IteratorCore<TermList>
  {
  public:
    NonVariableIterator(const Term* term) : _stack(8), _used(false)
    {
      pushNextNonVar(term->args());
    }

    bool hasNext();
    /** Return next non-variable subterm.
     * @warning hasNext() must have been called before */
    TermList next()
    {
      ASS(!_used && !_stack.top()->isVar());
      _used=true;
      return *_stack.top();
    }
  private:
    void pushNextNonVar(const TermList* t);

    Stack<const TermList*> _stack;
    bool _used;
  };

  /**
   * Iterator that iterator over disagreement set of two terms
   * or literals in DFS left to right order.
   */
  class DisagreementSetIterator
  : public IteratorCore<pair<TermList, TermList> >
  {
  public:
    DisagreementSetIterator(TermList t1, TermList t2, bool disjunctVariables=true)
    : _stack(8), _disjunctVariables(disjunctVariables)
    {
      CALL("Term::DisagreementSetIterator::DisagreementSetIterator(TermList...)");
      ASS(!t1.isEmpty());
      ASS(!t2.isEmpty());

      if(!TermList::sameTop(t1,t2)) {
	_arg1=t1;
	_arg2=t2;
	return;
      }
      _arg1.makeEmpty();
      if(t1.isTerm() && t1.term()->arity()>0) {
	_stack.push(t1.term()->args());
	_stack.push(t2.term()->args());
      }
    }
    /**
     * Create an iterator over the disagreement set of two terms/literals
     * with the same top functor.
     */
    DisagreementSetIterator(Term* t1, Term* t2, bool disjunctVariables=true)
    : _stack(8), _disjunctVariables(disjunctVariables)
    {
      ASS_EQ(t1->functor(), t2->functor());
      _arg1.makeEmpty();
      if(t1->arity()>0) {
	_stack.push(t1->args());
	_stack.push(t2->args());
      }
    }

    bool hasNext();

    /** Return next subterm
     * @warning hasNext() must have been called before */
    pair<TermList, TermList> next()
    {
      pair<TermList, TermList> res(_arg1,_arg2);
      _arg1.makeEmpty();
      return res;
    }
  private:
    Stack<TermList*> _stack;
    bool _disjunctVariables;
    TermList _arg1;
    TermList _arg2;
  };

  static Comparison lexicographicCompare(TermList t1, TermList t2);

  static Comparison lexicographicCompare(Term* t1, Term* t2);

  enum ArgumentOrder {
    UNKNOWN=0,
    LESS=1,
    EQUAL=2,
    GREATER=3,
    INCOMPARABLE=4
  };

  /** Return argument order as stored in term.
   * (Can also return UNKNOWN if it wasn't determined yet.) */
  bool askArgumentOrder(ArgumentOrder& res) const
  {
    res=static_cast<ArgumentOrder>(_args[0]._info.order);
    return res!=UNKNOWN;
  }
  ArgumentOrder getArgumentOrder()
  {
    if(static_cast<ArgumentOrder>(_args[0]._info.order)==UNKNOWN) {
      _args[0]._info.order=computeArgumentOrder();
    }
    return static_cast<ArgumentOrder>(_args[0]._info.order);
  }

  /** Return argument order as stored in term.
   * (Can also return UNKNOWN if it wasn't determined yet.) */
  bool askDistinctVars(unsigned& res) const
  {
    if(_args[0]._info.distinctVars==TERM_DIST_VAR_UNKNOWN) {
      return false;
    }
    res=_args[0]._info.distinctVars;
    return true;
  }
  unsigned getDistinctVars()
  {
    if(_args[0]._info.distinctVars==TERM_DIST_VAR_UNKNOWN) {
      unsigned res=computeDistinctVars();
      if(res<TERM_DIST_VAR_UNKNOWN) {
	_args[0]._info.distinctVars=res;
      }
      return res;
    } else {
      ASS_L(_args[0]._info.distinctVars,0x100000);
      return _args[0]._info.distinctVars;
    }
  }

  bool couldBeInstanceOf(Term* t)
  {
    ASS(shared());
    ASS(t->shared());
    if(t->functor()!=functor()) {
      return false;
    }
    ASS(!commutative());
    return couldArgsBeInstanceOf(t);
  }
  inline bool couldArgsBeInstanceOf(Term* t)
  {
#if USE_MATCH_TAG
    ensureMatchTag();
    t->ensureMatchTag();
    return matchTag().couldBeInstanceOf(t->matchTag());
#else
    return true;
#endif
  }

  bool containsSubterm(TermList v);


protected:
  ArgumentOrder computeArgumentOrder() const;
  unsigned computeDistinctVars() const;

#if USE_MATCH_TAG
  inline void ensureMatchTag()
  {
    matchTag().ensureInit(this);
  }

  inline MatchTag& matchTag()
  {
#if ARCH_X64
    return _args[0]._info.matchTag;
#else
    return _matchTag;
#endif
  }

#endif

  /** The number of this symbol in a signature */
  unsigned _functor;
  /** Arity of the symbol */
  unsigned _arity : 30;
  /** colour, used in interpolation and symbol elimination */
  unsigned _color : 2;
  /** Weight of the symbol */
  unsigned _weight;
  /** number of occurrences of variables */
  unsigned _vars;

#if USE_MATCH_TAG && !ARCH_X64
  MatchTag _matchTag;
#endif

  /** The list of arguments or size arity+1. The first argument stores the
   *  term weight and the mask (the last two bits are 0).
   */
  TermList _args[1];

  /** set the colour of the term */
  void setColor(unsigned color)
  {
    ASS(_color == 0 || _color == color);
    _color = color;
  } // setColor
  /** return the colour of the term */
  unsigned color() const { return _color; }

//   /** set all boolean fields to false and weight to 0 */
//   void initialise()
//   {
//     shared = 0;
//       ground = 0;
//       weight = 0;
//     }
//   };

//   Comparison compare(const Term* t) const;
//   void argsWeight(unsigned& total) const;
  friend class TermList;
  friend class MatchTag;
  friend class Indexing::TermSharing;
}; // class Term

/**
 * Class of literals.
 * @since 06/05/2007 Manchester
 */
class Literal
  : public Term
{
public:
  /** True if equality literal */
  bool isEquality() const
  { return functor() == 0; }

  Literal();
  explicit Literal(const Literal& l) throw();

  /**
   * Create a literal.
   * @since 16/05/2007 Manchester
   */
  Literal(unsigned functor,unsigned arity,bool polarity,bool commutative) throw()
  {
    _functor = functor;
    _arity = arity;
    _args[0]._info.polarity = polarity;
    _args[0]._info.commutative = commutative;
    _args[0]._info.literal = 1u;
  }

  /**
   * A unique header, 2*p is negative and 2*p+1 if positive where p is
   * the number of the predicate symbol.
   */
  unsigned header() const
  { return 2*_functor + polarity(); }
  /**
   * Header of the complementary literal, 2*p+1 is negative and 2*p
   * if positive where p is the number of the predicate symbol.
   */
  unsigned complementaryHeader() const
  { return 2*_functor + 1 - polarity(); }

  /**
   * Convert header to the correponding predicate symbol number.
   * @since 08/08/2008 flight Manchester-Singapore
   */
  static unsigned int headerToPredicateNumber(unsigned header)
  {
    return header/2;
  }
  /**
   * Convert header to the correponding polarity.
   * @since 08/08/2008 flight Manchester-Singapore
   */
  static unsigned int headerToPolarity(unsigned header)
  {
    return header % 2;
  }
  static bool headersMatch(Literal* l1, Literal* l2, bool complementary)
  {
    return l1->_functor==l2->_functor &&
      (complementary?1:0)==(l1->polarity()^l2->polarity());
  }
  /** Negate, should not be used with shared terms */
  void negate()
  {
    ASS(! shared());
    _args[0]._info.polarity = 1 - _args[0]._info.polarity;
  }
  /** set polarity to true or false */
  void setPolarity(bool positive)
  { _args[0]._info.polarity = positive ? 1 : 0; }
  static Literal* create(unsigned predicate, unsigned arity, bool polarity,
	  bool commutative, TermList* args);
  static Literal* create(Literal* l,bool polarity);
  static Literal* create(Literal* l,TermList* args);
  static Literal* createEquality (bool polarity, TermList arg1, TermList arg2);

  static Literal* flattenOnArgument(const Literal*,int argumentNumber);

  unsigned hash() const;
  /** true if positive */
  bool isPositive() const
  {
    return _args[0]._info.polarity;
  } // isPositive

  /** true if negative */
  bool isNegative() const
  {
    return ! _args[0]._info.polarity;
  } // isNegative

  /** return polarity, 1 if positive and 0 if negative */
  int polarity() const
  {
    return _args[0]._info.polarity;
  } // polarity

  /** Return a new equality literal */
  static inline Literal* equality (bool polarity)
  {
     CALL("Literal::equality/1");
     return new(2) Literal(0,2,polarity,true);
  }

//   /** Applied @b subst to the literal and return the result */
  Literal* apply(Substitution& subst);


  inline bool couldBeInstanceOf(Literal* lit, bool complementary)
  {
    ASS(shared());
    ASS(lit->shared());
    if(!headersMatch(this, lit, complementary)) {
      return false;
    }
    return couldArgsBeInstanceOf(lit);
  }
  bool couldArgsBeInstanceOf(Literal* lit)
  {
#if USE_MATCH_TAG
    ensureMatchTag();
    lit->ensureMatchTag();
    if(commutative()) {
      return matchTag().couldBeInstanceOf(lit->matchTag()) ||
	  matchTag().couldBeInstanceOfReversed(lit->matchTag());
    } else {
      return matchTag().couldBeInstanceOf(lit->matchTag());
    }
#else
    return true;
#endif
  }



//   XMLElement toXML() const;
  string toString() const;
  const string& predicateName() const;

}; // class Literal

std::ostream& operator<< (ostream& out, TermList tl );
std::ostream& operator<< (ostream& out, const Term& tl );
std::ostream& operator<< (ostream& out, const Literal& tl );

}
#endif
