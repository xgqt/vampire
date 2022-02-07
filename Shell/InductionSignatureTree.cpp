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
 * @file InductionSignatureTree.cpp
 * Implements class InductionSignatureTree.
 */

#include "InductionSignatureTree.hpp"
#include "Lib/Stack.hpp"
#include "Kernel/Signature.hpp"
#include "Lib/Environment.hpp"

namespace Shell
{

inline vstring skolemToString(unsigned f) {
  return env.signature->functionName(f);
}

inline vstring setToString(const vset<unsigned>& s) {
  vstringstream str;
  str << "{ ";
  for (const auto& c : s) {
    str << skolemToString(c) << ", ";
  }
  str << "}";
  return str.str();
}

InductionSignatureTree::~InductionSignatureTree() {
  Stack<Node*> todos;
  for (const auto& c : _root.children) {
    todos.push(c);
  }
  while (todos.isNonEmpty()) {
    auto curr = todos.pop();
    for (const auto& c : curr->children) {
      todos.push(c);
    }
    delete curr;
  }
}

bool InductionSignatureTree::add(vset<unsigned> olds, const vset<unsigned>& news) {
  Node* curr = &_root;
  // cout << "add: starting with " << setToString(olds) << ", " << setToString(news) << endl;
  while (curr) {
    Node* next = nullptr;
    for (auto it = curr->children.begin(); it != curr->children.end(); it++) {
      ASS(*it);
      if (!(*it)->all.count(*olds.begin())) {
        continue;
      }
#if VDEBUG
      for (const auto& o : olds) {
        ASS((*it)->all.count(o));
      }
      // check that there is no intersection with other children
      for (auto it2 = it+1; it2 != curr->children.end(); it2++) {
        vset<unsigned> temp;
        set_intersection((*it2)->all.begin(), (*it2)->all.end(),
          olds.begin(), olds.end(), inserter(temp, temp.begin()));
        ASS(temp.empty());
      }
#endif
      vset<unsigned> diff;
      set_difference(olds.begin(), olds.end(), (*it)->data.begin(), (*it)->data.end(),
        inserter(diff, diff.begin()));
      olds = diff;
      // cout << "remaining " << setToString(olds) << endl;
      next = *it;
      for (const auto& n : news) {
        (*it)->all.insert(n);
      }
      break;
    }
    if (!next) {
      if (!olds.empty()) {
        return false;
      }
      next = new Node();
      next->data = news;
      next->all = news;
      // cout << "new node " << setToString(next->data) << endl;
      curr->children.push_back(next);
      curr = nullptr;
      break;
    }
    curr = next;
  }
  return true;
}

bool InductionSignatureTree::isConflicting(vset<unsigned> s) const {
  if (s.empty()) {
    return false;
  }
  const Node* curr = &_root;
  // cout << "isConflicting: starting with " << setToString(s) << endl;
  while (curr) {
    Node* next = nullptr;
    for (auto it = curr->children.begin(); it != curr->children.end(); it++) {
      ASS(*it);
      if (!(*it)->all.count(*s.begin())) {
        continue;
      }
#if VDEBUG
      for (const auto& e : s) {
        ASS((*it)->all.count(e));
      }
      // check that there is no intersection with other children
      for (auto it2 = it+1; it2 != curr->children.end(); it2++) {
        vset<unsigned> temp;
        set_intersection((*it2)->all.begin(), (*it2)->all.end(),
          s.begin(), s.end(), inserter(temp, temp.begin()));
        ASS(temp.empty());
      }
#endif
      vset<unsigned> diff;
      set_difference(s.begin(), s.end(), (*it)->data.begin(), (*it)->data.end(),
        inserter(diff, diff.begin()));
      s = diff;
      // cout << "remaining " << setToString(s) << endl;
      next = *it;
      break;
    }
    curr = next;
  }
  // if (!s.empty()) {
  //   cout << "conflict " << setToString(s) << endl;
  // }
  return !s.empty();
}

}
