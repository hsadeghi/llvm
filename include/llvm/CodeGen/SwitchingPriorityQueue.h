//===--- SwitchingPriorityQueue.h - A latency-oriented priority queue -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// SwitchingPriorityQueue attempts to reduce the switching costs in adjacent
// instructions.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_SWITCHINGPRIORITYQUEUE_H
#define LLVM_CODEGEN_SWITCHINGPRIORITYQUEUE_H

#include "llvm/CodeGen/ScheduleDAG.h"
#include "llvm/Support/raw_ostream.h"

namespace llvm {

class SwitchingPriorityQueue : public SchedulingPriorityQueue {
 public:
  virtual bool isBottomUp() const { return false; }
  virtual void initNodes(std::vector<SUnit> &) { }
  virtual void addNode(const SUnit *) { }
  virtual void updateNode(const SUnit *) { }
  virtual void releaseState() { unitsAlreadyScheduled.clear(); }

  virtual bool empty() const { return queue.empty(); }
  virtual void push(SUnit *node) { queue.push_back(node); }

  virtual void scheduledNode(SUnit *SU);
  virtual void unscheduledNode(SUnit *SU);

  virtual SUnit *pop();
  virtual void remove(SUnit *SU) { removeFrom(queue, SU); }

private:
  std::vector<SUnit *> queue;
  std::vector<SUnit *> unitsAlreadyScheduled;

  void removeFrom(std::vector<SUnit *> &, const SUnit *);
};

}

#endif // LLVM_CODEGEN_SWITCHINGPRIORITYQUEUE_H
