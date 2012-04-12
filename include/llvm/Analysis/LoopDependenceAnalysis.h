//===- llvm/Analysis/LoopDependenceAnalysis.h --------------- -*- C++ -*---===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// LoopDependenceAnalysis is an LLVM pass that analyses dependences in memory
// accesses in loops.
//
// Please note that this is work in progress and the interface is subject to
// change.
//
// TODO: adapt as interface progresses
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_LOOP_DEPENDENCE_ANALYSIS_H
#define LLVM_ANALYSIS_LOOP_DEPENDENCE_ANALYSIS_H

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/FoldingSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Support/Allocator.h"

namespace llvm {

// TODO: Rename class
// TODO: rename a and b to src and dest

class AliasAnalysis;
class AnalysisUsage;
class ScalarEvolution;
class SCEV;
class TargetData;
class Value;
class raw_ostream;

class LoopDependenceAnalysis : public LoopPass {
  AliasAnalysis *AA;
  ScalarEvolution *SE;
  LoopInfo *LI;

  /// L - The loop we are currently analysing.
  Loop *L;
public:

  struct Level {
    enum { NONE = 0, LT  = 1, EQ  = 2, GT  = 4, ALL = 7 };
    int direction;
    bool scalar;
    const SCEV *distance; // NULL implies no distance available

    Level() : direction(ALL), scalar(true), distance(NULL) { }

    void intersect(const Level &level);
  };

  class Dependence {
  public:
    enum Result { Independent, Dependent };

    Result getResult() const {
      return result;
    }

    const Value *getSource() const {
      return source;
    }

    const Value *getDestination() const {
      return destination;
    }

    typedef SmallVector<const Level, 4>::const_iterator const_iterator;
    const_iterator begin() const { return levels.begin(); }
    const_iterator end() const { return levels.end(); }

    explicit Dependence(int numLevels) : levels(numLevels),
                                         result(Dependent)
      { }

  private:
    Value *source, *destination;
    SmallVector<Level, 4> levels;
    Result result;

    friend class LoopDependenceAnalysis;
  };

private:
  /// DependencePair - Represents a data dependence relation between to memory
  /// reference instructions.
  struct DependencePair : public FastFoldingSetNode {
    Value *destination;
    Value *source;
    Dependence *result;

    DependencePair(const FoldingSetNodeID &ID, Value *dest, Value *src) :
      FastFoldingSetNode(ID), destination(dest), source(src) {}
  };

  /// findOrInsertDependencePair - Return true if a DependencePair for the
  /// given Values already exists, false if a new DependencePair had to be
  /// created. The third argument is set to the pair found or created.
  bool findOrInsertDependencePair(Value *, Value *, DependencePair *&);

  /// getLoops - Collect all loops of the loop nest L in which
  /// a given SCEV is variant.
  void getLoops(const SCEV *, DenseSet<const Loop *> *) const;

  /// isLoopInvariant - True if a given SCEV is invariant in all loops of the
  /// loop nest starting at the innermost loop L.
  bool isLoopInvariant(const SCEV *) const;

  /// Tries to break an add recurrence into a pair of SCEVs A and B such that
  /// the value of the add recurrence is (A * I + B) where I is the loop
  /// induction variable and A and B are loop invariant expressions.  This also
  /// computes the loop the add recurrence belongs to.  Returns true on success
  /// and false if it is unable to break up the SCEV.
  bool getLinearExpression(const SCEV *X, const SCEV **, const SCEV **,
                           const Loop **) const;

  /// These functions return true if they could analyse the subscript pair in a
  /// meaningful way.
  bool analyseZIV(const SCEV *, const SCEV *, Level *, bool *) const;
  bool analyseSIV(const SCEV *, const SCEV *, Level *, bool *) const;

  bool analyseStrongSIV(const SCEV *, const SCEV *, const SCEV *, const SCEV *,
                        const Loop *, Level *) const;
  bool analyseWeakZeroSIV(const SCEV *, const SCEV *, const SCEV *,
                          const SCEV *, const Loop *, Level *) const;
  bool analyseWeakCrossingSIV(const SCEV *, const SCEV *, const SCEV *,
                              const SCEV *, const Loop *, Level *) const;

  /// true on dependence, false in proven independence
  bool analyseSubscript(const SCEV *, const SCEV *, Level *,
                        const Loop **) const;

  Dependence *analysePair(Value *, Value *) const;

public:
  static char ID; // Class identification, replacement for typeinfo
  LoopDependenceAnalysis() : LoopPass(ID) {
    initializeLoopDependenceAnalysisPass(*PassRegistry::getPassRegistry());
  }

  /// depends - Return a boolean indicating if there is a data dependence
  /// between two instructions.
  Dependence *depends(Value *destination, Value *source);

  bool runOnLoop(Loop *, LPPassManager &);
  virtual void releaseMemory();
  virtual void getAnalysisUsage(AnalysisUsage &) const;
  void print(raw_ostream &, const Module * = 0) const;
  bool isDependencePair(const Value *A, const Value *B) const;

private:
  FoldingSet<DependencePair> Pairs;
  BumpPtrAllocator PairAllocator;
}; // class LoopDependenceAnalysis

// createLoopDependenceAnalysisPass - This creates an instance of the
// LoopDependenceAnalysis pass.
//
LoopPass *createLoopDependenceAnalysisPass();

} // namespace llvm

#endif /* LLVM_ANALYSIS_LOOP_DEPENDENCE_ANALYSIS_H */
