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
#include "llvm/Support/MathExtras.h"

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

    int leftScore = hammingScore(left->getInstr(), previousInst->getInstr());
    int rightScore = hammingScore(right->getInstr(), previousInst->getInstr());

    if (leftScore < rightScore) /* left is more expensive */ return false;
    if (leftScore > rightScore) return true;

    return left->NodeNum < right->NodeNum;
  }

  bool getOnlyImmOperand(const MachineInstr *instr, int64_t *out_value) const {
    bool found = false;
    int64_t value = 0;
    for (MachineInstr::const_mop_iterator I = instr->operands_begin(),
           E = instr->operands_end();
         I != E;
         ++I) {
      if (I->isImm()) {
        if (found) return false; // More than one immediate operand

        found = true;
        value = I->getImm();
      }
    }
    *out_value = value;
    return true;
  }

  int hammingScore(const MachineInstr *a, const MachineInstr *b) const {
    int score = 0;
    if (a->getOpcode() == b->getOpcode()) score += kSameOp;
    int64_t a_imm = 0, b_imm = 0;

    getOnlyImmOperand(a, &a_imm);
    getOnlyImmOperand(b, &b_imm);

    score += kImmXorOnes * CountPopulation_64(a_imm ^ b_imm);

    return score;
  }

  enum ScoreWeights {
    kSameOp = 30,
    kImmXorOnes = -2
  };
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
