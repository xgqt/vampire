/**
 * @file SkipList.hpp
* Implements skip lists storing a key and a value.
 *
 * @since 03/05/2006 Bellevue
 */


#ifndef __SkipList__
#  define __SkipList__

#include "../Debug/Assertion.hpp"
#include "../Debug/Tracer.hpp"

#include "Allocator.hpp"
#include "Comparison.hpp"
#include "Random.hpp"
#include "BacktrackData.hpp"

#define SKIP_LIST_MAX_HEIGHT 32

namespace Lib
{

/**
 * Skip lists storing a value of class Value.
 * The class ValueComparator should contain a function compare used to
 * compare Values.
 * @since 04/05/2006 Bellevue
 */
template <class Value,class ValueComparator>
class SkipList
{
public:
  class Node {
  public:
    Value value;
    Node* nodes[1];
  };
  /**
   * Insert an element in the skip list.
   * @since 04/05/2006 Bellevue
   */
  inline
  void insert(Value val)
  {
    CALL("SkipList::insert");
    Value* pval=insertPosition(val);
    *pval=val;
  } // SkipList::insert


  /**
   * If value with given key is present, assign pointer to the
   * value into @b pvalue and return true.
   * If the value is not present, return false, and if @b canCreate
   * is true, create a Node where a value with given key could be
   * stored, and assign pointer to value in that Node into @b pvalue.
   *
   * Type Key has to be supported by ValueComparator. I.e. it must
   * contain method Comparison compare(Key,Value).
   */
  template<typename Key>
  bool getPosition(Key key, Value*& pvalue, bool canCreate)
  {
    CALL("SkipList::getPosition");

    if(_top==0) {
      if(canCreate) {
	pvalue=insertPosition(key);
      }
      return false;
    }

    unsigned h=_top-1;

   // left is a node with a value smaller than that of newNode and having
    // a large enough height.
    // this node is on the left of the inserted one
    Node* left = _left;
    for (;;) {
      Node* next = left->nodes[h];
      if (next == 0) {
	if (h == 0) {
	    if(canCreate) {
	      pvalue=insertPosition(key);
	    }
	    return false;
	}
	h--;
	continue;
      }
      // next != 0
      switch (ValueComparator::compare(key,next->value))
	{
	case LESS:
	  // the node should be inserted on the left
	  if (h == 0) {
	    if(canCreate) {
	      pvalue=insertPosition(key);
	    }
	    return false;
	  }
	  h--;
	  break;

	case EQUAL:
	  pvalue=&next->value;
	  return true;

	case GREATER:
	  left = next;
	  break;

#if VDEBUG
	default:
	  ASSERTION_VIOLATION;
#endif
	}
    }
  } // SkipList::getPosition

  /**
   * Create Node where a value with given key could be
   * stored, and assign pointer to value in that Node into @b pvalue.
   *
   * Type Key has to be supported by ValueComparator. I.e. it must
   * contain method Comparison compare(Key,Value).
   */
  template<typename Key>
  Value* insertPosition(Key key)
  {
    CALL("SkipList::insertPosition");

    // select a random height between 0 and top
    unsigned nodeHeight = 0;
    while (Random::getBit()) {
      nodeHeight++;
    }
    if (nodeHeight >= _top) {
      if (_top < SKIP_LIST_MAX_HEIGHT) {
	nodeHeight = _top;
	_top++;
      }
      else {
	ASS(_top == SKIP_LIST_MAX_HEIGHT);
	nodeHeight = _top - 1;
      }
    }
    Node* newNode = allocate(nodeHeight);
    new(&newNode->value) Value();


    unsigned h = _top - 1;


    // left is a node with a value smaller than that of newNode and having
    // a large enough height.
    // this node is on the left of the inserted one
    Node* left = _left;
    for (;;) {
      Node* next = left->nodes[h];
      if (next == 0) {
	if(h<=nodeHeight) {
	  left->nodes[h] = newNode;
	  newNode->nodes[h] = 0;
	  if (h == 0) {
	    return &newNode->value;
	  }
	}
	h--;
	continue;
      }
      // next != 0
      switch (ValueComparator::compare(key,next->value))
	{
	case LESS:
	  // the node should be inserted on the left
	  if(h<=nodeHeight) {
	    newNode->nodes[h] = next;
	    left->nodes[h] = newNode;
	    if (h == 0) {
	      return &newNode->value;
	    }
	  }
	  h--;
	  break;

	case EQUAL: //we insert equal elements next to each other
	case GREATER:
	  left = next;
	  break;

#if VDEBUG
	default:
	  ASSERTION_VIOLATION;
#endif
	}
    }
  } // SkipList::insertPosition

  /**
   * Return number of elements in the SkipList.
   *
   * The method works in linear time with the
   * size of skip list, so should be used for
   * debugging purposes only.
   */
  int size() const
  {
    int res=0;
    Iterator it(*this);
    while(it.hasNext()) {
      it.next();
      res++;
    }
    return res;
  }

  /**
   * True if the list is empty.
   * @since 04/05/2006 Bellevue
   */
  inline
  bool isEmpty() const
  {
    return _left->nodes[0] == 0;
  } // SkipList::isEmpty

  /**
   * True if the list is not empty.
   * @since 04/05/2006 Bellevue
   */
  inline
  bool isNonEmpty() const
  {
    return _left->nodes[0] != 0;
  } // SkipList::isNonEmpty

  /** Returns the first element without removing it. */
  inline
  const Value& top()
  {
    ASS(isNonEmpty());
    return _left->nodes[0]->value;
  }

  /**
   * Pop the first element.
   * @since 04/05/2006 Bellevue
   */
  Value pop()
  {
    CALL("SkipList::pop");
    ASS(isNonEmpty());

    // find the height of the first
    Node* node = _left->nodes[0];
    unsigned h;
    for (h = 1;h < _top;h++) {
      if (_left->nodes[h] != node) {
	break;
      }
    }
    // the height of the first node is h-1
    for (unsigned i = 0;i < h;i++) {
      _left->nodes[i] = node->nodes[i];
    }
    Value val = node->value;
    deallocate(node,h-1);
    return val;
  } // SkipList::pop

  /**
   * Remove value matching the key from the list.
   *
   * Type Key has to be supported by ValueComparator. I.e. it must
   * contain method Comparison compare(Key,Value).
   * @since 04/05/2006 Bellevue
   */
  template<typename Key>
  void remove(Key key)
  {
    CALL("SkipList::remove");
    ASS(_top > 0);

    Node* found = 0; // found node
#if VDEBUG
    unsigned foundHeight = 0; // its height
#else
    unsigned foundHeight; // its height
#endif

    Node* left = _left;
    unsigned h = _top-1;
    for (;;) {
      Node* next = left->nodes[h];
      if (next == 0) {
	ASS(h != 0);
	h--;
	continue;
      }
      // next != 0
      switch (ValueComparator::compare(key,next->value))
	{
	case LESS:
	  ASS(h != 0);
	  h--;
	  break;

	case GREATER:
	  left = next;
	  break;

	case EQUAL:
	  found = next;
	  foundHeight = h;
	  if(h>0 && found->nodes[0] && found->nodes[h]!=found->nodes[0] &&
		  ValueComparator::compare(key,found->nodes[0]->value)==EQUAL) {
	    //The next element exists, contains the same value,
	    //and its height is lower that the height of this one.
	    //We'll rather delete that one, tha the one we've found,
	    //because otherwise there'd be only low elements after a few
	    //deletions, which would degrade the skip list to linked list.
	    h=0;
	    while(found->nodes[0]==found->nodes[h+1]) {
	      h++;
	    }
	    left = found;
	    found = found->nodes[0];
	    foundHeight = h;
	  }
	  for(;;) {
	    left->nodes[h] = found->nodes[h];
	    if(h==0) {
	      break;
	    }
	    h--;
	    while(left->nodes[h]!=found) {
	      left=left->nodes[h];
	      ASS(ValueComparator::compare(key,left->value)!=LESS);
	    }
	  }

	  deallocate(found,foundHeight);
	  return;

#if VDEBUG
	default:
	  ASSERTION_VIOLATION;
#endif
	}
    }
  } // SkipList::remove

  template<typename Key>
  inline
  bool find(Key key)
  {
    Value* pval;
    return getPosition(key,pval,false);
  }

  template<typename Key>
  inline
  bool find(Key key, Value& val)
  {
    Value* pval;
    bool res=getPosition(key,pval,false);
    val=*pval;
    return res;
  }


  inline
  void makeEmpty()
  {
    while (isNonEmpty()) {
      pop();
    }
  }

  /**
   * Create a skip list and initialise its left-most node to a node of the
   * maximal possible height.
   * @since 04/05/2006 Bellevue
   */
  SkipList()
    : _left(allocate(SKIP_LIST_MAX_HEIGHT)),
      _top(0)
  {
    CALL("SkipList::SkipList");
    for (int h = SKIP_LIST_MAX_HEIGHT-1;h >= 0;h--) {
      _left->nodes[h] = 0;
    }
  }
  /**
   * Destroy the skip list.
   * @since 04/05/2006 Bellevue
   */
  ~SkipList()
  {
    CALL("SkipList::~SkipList");

    makeEmpty();
    deallocate(_left,SKIP_LIST_MAX_HEIGHT);
  }
private:
  /** the leftmost node with the dummy key and value */
  Node* _left;
  /** the largest height of nodes + 1 */
  unsigned _top;

  /** allocate node of height h */
  inline
  static Node* allocate(unsigned h)
  {
    CALL("SkipList::allocate");

    void* memory = ALLOC_KNOWN(sizeof(Node)+h*sizeof(Node*),"SkipList::Node");

    return reinterpret_cast<Node*>(memory);
  }

  /** deallocate node of height h */
  inline
  static void deallocate(Node* node,unsigned h)
  {
    CALL("SkipList::deallocate");
    DEALLOC_KNOWN(node,sizeof(Node)+h*sizeof(Node*),"SkipList::Node");
  }


  class SingleValBacktrackObject: public BacktrackObject
  {
  public:
    enum Action {
      REMOVE, INSERT
    };
    SingleValBacktrackObject(SkipList* sl, Action a, Value v): sl(sl), a(a), v(v) {}
    void backtrack()
    {
      switch(a) {
      case REMOVE:
	sl->insert(v);
	break;
      case INSERT:
	sl->remove(v);
	break;
      default:
	ASSERTION_VIOLATION;
      }
    }
  private:
    SkipList* sl;
    Action a;
    Value v;
  };
public:
  Value backtrackablePop(BacktrackData& bd)
  {
    Value v=pop();
    bd.addBacktrackObject(
	    new SingleValBacktrackObject(this, SingleValBacktrackObject::REMOVE, v));
    return v;
  }
  void backtrackableInsert(Value v, BacktrackData& bd)
  {
    insert(v);
    bd.addBacktrackObject(
	    new SingleValBacktrackObject(this, SingleValBacktrackObject::INSERT, v));
  }

public:

  /** iterator over the skip list elements */
  class Iterator {
   public:

    inline explicit
    Iterator(const SkipList& l)
      : _cur (l._left)
    {}

    /** return the next element */
    inline Value next()
    {
      ASS(_cur->nodes[0]);
      _cur=_cur->nodes[0];
      return _cur->value;
    }

    /** True if there is a next element. */
    inline bool hasNext() const
    {
      return _cur->nodes[0];
    }

   private:
    /** the node we're now pointing to */
    Node* _cur;
  };

  /**
   * Iterator over the skip list elements,
   * which yields pointers to elements.
   */
  class PtrIterator {
   public:

    inline explicit
    PtrIterator(const SkipList& l)
      : _cur (l._left)
    {}

    /** return the next element */
    inline Value* next()
    {
      ASS(_cur->nodes[0]);
      _cur=_cur->nodes[0];
      return &_cur->value;
    }

    /** True if there is a next element. */
    inline bool hasNext() const
    {
      return _cur->nodes[0];
    }

   private:
    /** the node we're now pointing to */
    Node* _cur;
  };


}; // class SkipList


} // namespace Lib
#endif


