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
 * @file InductionSignatureTree.hpp
 * Defines class InductionSignatureTree.
 */

#ifndef __InductionSignatureTree__
#define __InductionSignatureTree__

#include "Forwards.hpp"

#include "Lib/STL.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class InductionSignatureTree {
public:
  ~InductionSignatureTree();
  bool add(vset<unsigned> olds, const vset<unsigned>& news);
  bool isConflicting(vset<unsigned> s) const;
private:
  struct Node {
    CLASS_NAME(Node);
    USE_ALLOCATOR(Node);

    vvector<Node*> children;
    vset<unsigned> data;
    vset<unsigned> all;
  };
  Node _root;
};

}

#endif // __InductionSignatureTree__
