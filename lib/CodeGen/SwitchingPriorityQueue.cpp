//===--- SwitchingPriorityQueue.cpp - A latency-oriented priority queue ---===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//


#define DEBUG_TYPE "switching-scheduler"
#include "llvm/CodeGen/SwitchingPriorityQueue.h"
#include "llvm/Support/Debug.h"

using namespace llvm;
using namespace std;

struct CompareSwitching {
  SUnit *previousInst;
  int previousOpcode;

  explicit CompareSwitching(SUnit *previous) : previousInst(previous) {
    assert(previousInst->isInstr());
    previousOpcode = previousInst->getInstr()->getOpcode();
  }

  bool operator()(SUnit *left, SUnit *right) const {
    // Check if Cost(left) < Cost(right)
    assert(left->isInstr());
    assert(right->isInstr());

    int leftOp = left->getInstr()->getOpcode();
    int rightOp = right->getInstr()->getOpcode();

    if (leftOp == previousOpcode && rightOp != previousOpcode) {
      return true;
    }
    if (leftOp != previousOpcode && rightOp == previousOpcode) {
      return false;
    }

    return right->NodeNum < left->NodeNum;
  }
};

void SwitchingPriorityQueue::scheduledNode(SUnit *SU) {
  unitsAlreadyScheduled.push_back(SU);
}

void SwitchingPriorityQueue::unscheduledNode(SUnit *SU) {
  removeFrom(unitsAlreadyScheduled, SU);
}

SUnit *SwitchingPriorityQueue::pop() {
  assert(!queue.empty());
  vector<SUnit *>::iterator candidate = prior(queue.end());

  if (!unitsAlreadyScheduled.empty()) {
    CompareSwitching comparator(unitsAlreadyScheduled.back());
    candidate = min_element(queue.begin(), queue.end(), comparator);
  }

  SUnit *result = *candidate;
  if (candidate != prior(queue.end())) {
    swap(*candidate, queue.back());
  }
  queue.pop_back();
  return result;
}

void SwitchingPriorityQueue::removeFrom(std::vector<SUnit *> &stack,
                                        const SUnit *SU) {
  std::vector<SUnit *>::iterator location =
    std::find(stack.begin(), stack.end(), SU);
  assert(location != stack.end() && "SUnit not in queue!");

  if (location != prior(stack.end()))
      std::swap(*location, stack.back());
  stack.pop_back();
}
