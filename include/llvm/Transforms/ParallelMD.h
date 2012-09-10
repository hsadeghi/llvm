//=- llvm/Transforms/ParallelMD.h - Parallel Metadata --*- C++ -*-=//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// TODO: Overview
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_PARALLEL_MD_H
#define LLVM_TRANSFORMS_PARALLEL_MD_H

#include "llvm/Pass.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Support/Allocator.h"

#include <list>

namespace llvm {

class Instruction;
class MDNode;

/// A ParallelMD class provides an interface to the !parallel metadata nodes in
/// the LLVM IR.
class ParallelMD {
public:

  /// The types of nodes the !parallel directive recognizes.
  enum MDKind {
    /// A block or region of code that is executed once by each thread in the
    /// current team.  These can be nested.
    /// Syntax:
    /// !{ metadata !"region", functionBody,
    ///             [ list of nested special regions ] }
    REGION,

    /// A sub-region in a parallel region that is executed only by one thread in
    /// the team.
    /// Syntax:
    /// !{ metadata !"serial", functionBody, parentMetadata,
    ///             ( !"master" | !"any" )
    SERIAL,

    /// A sub-region in a parallel region that is executed by all threads in the
    /// team with mutual exclusion.
    /// Syntax:
    /// !{ metadata !"critical", functionBody, parentMetadata, "tag" }
    CRITICAL,

    /// A sub-region in a parallel for that is executed in the original
    /// iteration order.
    /// Syntax:
    /// !{ metadata !"ordered", functionBody, parentLoopMetadata }
    ORDERED,

    /// A sub-region in a parallel region whose iterations may be run in
    /// parallel.
    /// Syntax:
    /// !{ metadata !"loop", parentRegionMetadata, ( !"static" | !"guided" |
    ///             !"dynamic" | !"runtime" | !"auto" ) integerLevel [ list of
    ///             !nested special regions ] }
    LOOP,

    /// A block of code that is executed by a thread in the current team,
    /// possibly asynchronously.
    /// Syntax:
    /// !{ metdata !"task", functionBody, parentMetadata,
    ///            ( !"untied" | !"tied" ), [ list of nested special regions ]
    TASK,

    MD_KIND_MAX
  };

  MDKind getKind() const { return type; }

  /// Methods for support type inquiry through isa, cast, and dyn_cast:
  static inline bool classof(const ParallelMD *region) { return true; }

protected:
  explicit ParallelMD(MDKind regionType) : type(regionType) { }

private:
  MDKind type;
};


/// A helper class for maintaining lists of special regions.
class MDSpecialChildrenHelper {
public:
  typedef std::list<ParallelMD *>::iterator iterator;
  typedef std::list<ParallelMD *>::const_iterator const_iterator;

  const_iterator begin() const { return children.begin(); }
  const_iterator end() const { return children.end(); }

  iterator begin() { return children.begin(); }
  iterator end() { return children.end(); }

protected:
  std::list<ParallelMD *> children;

  friend class ParallelizationMetadata;
};


class RegionMD : public ParallelMD, public MDSpecialChildrenHelper {
public:
  RegionMD() : ParallelMD(REGION) { }

  Function *getBody() const { return body; }

  static inline bool classof(const RegionMD *region) { return true; }
  static inline bool classof(const ParallelMD *md) {
    return md->getKind() == REGION;
  }

private:
  Function *body;

  friend class ParallelizationMetadata;
};


class SerialMD : public ParallelMD {
public:
  SerialMD() : ParallelMD(SERIAL) { }

  enum Kind { MASTER, ANY };
  Function *getBody() const { return body; }
  Kind getKind() const { return kind; }
  ParallelMD *getParent() const { return parent; }

  static inline bool classof(const SerialMD *serial) { return true; }
  static inline bool classof(const ParallelMD *md) {
    return md->getKind() == SERIAL;
  }

private:
  Function *body;
  ParallelMD *parent;
  Kind kind;

  friend class ParallelizationMetadata;
};


class CriticalMD : public ParallelMD {
public:
  CriticalMD() : ParallelMD(CRITICAL) { }

  Function *getBody() const { return body; }
  ParallelMD *getParent() const { return parent; }
  StringRef getTag() const { return tag; }

  static inline bool classof(const CriticalMD *critical) { return true; }
  static inline bool classof(const ParallelMD *md) {
    return md->getKind() == CRITICAL;
  }

private:
  Function *body;
  ParallelMD *parent;
  StringRef tag;

  friend class ParallelizationMetadata;
};


class LoopMD : public ParallelMD {
public:
  LoopMD() : ParallelMD(LOOP) { }

  enum Schedule { STATIC, DYNAMIC, GUIDED, RUNTIME, AUTO };

  RegionMD *getParent() const { return parent; }
  Schedule getSchedule() const { return schedule; }
  int getLevels() const { return levels; }

  static inline bool classof(const LoopMD *loop) { return true; }
  static inline bool classof(const ParallelMD *md) {
    return md->getKind() == LOOP;
  }

private:
  RegionMD *parent;
  Schedule schedule;
  int levels;

  friend class ParallelizationMetadata;
};


class OrderedMD : public ParallelMD {
public:
  OrderedMD() : ParallelMD(ORDERED) { }

  Function *getBody() const { return body; }
  LoopMD *getParentLoop() const { return parent; }

  static inline bool classof(const OrderedMD *ordered) { return true; }
  static inline bool classof(const ParallelMD *md) {
    return md->getKind() == ORDERED;
  }

private:
  Function *body;
  LoopMD *parent;

  friend class ParallelizationMetadata;
};


class TaskMD : public ParallelMD, public MDSpecialChildrenHelper {
public:
  TaskMD() : ParallelMD(ParallelMD::TASK) { }

  enum Affinity { TIED, UNTIED };

  Function *getBody() const { return body; }
  ParallelMD *getParentRegion() const { return parent; }
  Affinity getAffinity() const { return affinity; }

  static inline bool classof(const TaskMD *task) { return true; }
  static inline bool classof(const ParallelMD *md) {
    return md->getKind() == TASK;
  }

private:
  Function *body;
  ParallelMD *parent;
  Affinity affinity;

  friend class ParallelizationMetadata;
};


/// This pass cleans up inconsistent parallel metadata and provides a clean
/// interface to access the same.
class ParallelizationMetadata : public ModulePass {
public:
  static char ID;

  ParallelizationMetadata() : ModulePass(ID) { }

  virtual bool runOnModule(Module &module);
  virtual void getAnalysisUsage(AnalysisUsage &AU);

  ParallelMD *metadataForInstruction(Instruction *instr) {
    DenseMap<const Instruction *, ParallelMD *>::iterator it =
      instructionMap.find(instr);
    if (it == instructionMap.end()) return NULL;
    return it->second;
  }

private:
  DenseMap<const Instruction *, ParallelMD *> instructionMap;
  BumpPtrAllocator allocator;

  // This points to a stack-allocated object during runOnModule and is NULL
  // otherwise.
  DenseMap<MDNode *, ParallelMD *> *rawNodeMap;

  ParallelMD *createParallelMD(MDNode *node);

  RegionMD *createRegionMD(MDNode *node);
  SerialMD *createSerialMD(MDNode *node);
  CriticalMD *createCriticalMD(MDNode *node);
  OrderedMD *createOrderedMD(MDNode *node);
  LoopMD *createLoopMD(MDNode *node);
  TaskMD *createTaskMD(MDNode *node);

  bool addSpecialRegions(ParallelMD *node, MDNode *rawNode, Function *body,
                         unsigned beginIdx);
};


}


#endif // LLVM_TRANSFORMS_PARALLEL_MD_H
