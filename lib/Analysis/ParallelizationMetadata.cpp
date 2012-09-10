//===- ParallelizationMetadata.cpp - 
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

#include "llvm/Transforms/ParallelMD.h"

#include "llvm/Function.h"
#include "llvm/InitializePasses.h"
#include "llvm/Instruction.h"
#include "llvm/Instructions.h"
#include "llvm/Metadata.h"
#include "llvm/Module.h"
#include "llvm/PassRegistry.h"

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringRef.h"

#include <cstdio>

using namespace llvm;
using namespace std;

char ParallelizationMetadata::ID = 0;
INITIALIZE_PASS(ParallelizationMetadata, "parallizationcleanup",
                "Clean up !parallel metadata", true, true)


static int SearchNodes(Function *function,
                       DenseMap<MDNode *, bool> &nodesToFind,
                       DenseSet<Function *> &inStack) {
  StringRef parallelTag = "parallel";
  int count = 0;
  for (Function::iterator BI = function->begin(), BE = function->end();
       BI != BE; ++BI) {
    for (BasicBlock::iterator I = BI->begin(), E = BI->end();
         I != E; ++I) {
      if (MDNode *node = I->getMetadata(parallelTag)) {
        if (nodesToFind[node]) {
          count++;
          nodesToFind[node] = true;
        }
      } else if (CallInst *callInst = dyn_cast<CallInst>(I)) {
        Function *callee = callInst->getCalledFunction();
        if (!callee || inStack.count(callee))
          continue;

        inStack.insert(function);
        count += SearchNodes(callee, nodesToFind, inStack);
        inStack.erase(function);
      }
    }
  }

  return count;
}


static ParallelMD::MDKind GetNodeKind(MDNode *node) {
  static const StringRef regionTag = "region",
    serialTag = "serial",
    criticalTag = "critical",
    orderedTag = "ordered",
    loopTag = "loop",
    taskTag = "task";

  if (node->getNumOperands() == 0)
    return ParallelMD::MD_KIND_MAX;

  MDString *mdString = dyn_cast<MDString>(node->getOperand(0));
  if (mdString == NULL)
    return ParallelMD::MD_KIND_MAX;

  StringRef string = mdString->getString();
  if (string == regionTag) {
    return ParallelMD::REGION;
  } else if (string == serialTag) {
    return ParallelMD::SERIAL;
  } else if (string == criticalTag) {
    return ParallelMD::CRITICAL;
  } else if (string == orderedTag) {
    return ParallelMD::ORDERED;
  } else if (string == loopTag) {
    return ParallelMD::LOOP;
  } else if (string == taskTag) {
    return ParallelMD::TASK;
  } else {
    return ParallelMD::MD_KIND_MAX;
  }
}


static ParallelMD *GetParentIfPossible(ParallelMD *node) {
  switch (node->getKind()) {
  case ParallelMD::SERIAL: return cast<SerialMD>(node)->getParent();
  case ParallelMD::CRITICAL: return cast<CriticalMD>(node)->getParent();
  case ParallelMD::ORDERED: return cast<OrderedMD>(node)->getParentLoop();
  default: return NULL;
  }
}


bool ParallelizationMetadata::addSpecialRegions(
  ParallelMD *node, MDNode *rawNode, Function *body, unsigned beginIdx) {
  // Return early, there's nothing to add.
  if (beginIdx == rawNode->getNumOperands()) return true;

  DenseMap<MDNode *, bool> specialList;

  for (unsigned i = beginIdx; i < rawNode->getNumOperands(); i++) {
    MDNode *nodeOperand = dyn_cast<MDNode>(rawNode->getOperand(i));
    if (nodeOperand == NULL) return false;

#ifdef DEBUG
    ParallelMD::MDKind nodeKind = GetNodeKind(nodeOperand);

    bool isAdmissible = nodeKind == ParallelMD::SERIAL ||
      nodeKind == ParallelMD::CRITICAL ||
      nodeKind == ParallelMD::ORDERED;

    assert(isAdmissible && "expected special-handling region");
#endif

    specialList[nodeOperand] = false;
  }

  DenseSet<Function *> currentlyInStack;
  unsigned nodesFound = SearchNodes(body, specialList, currentlyInStack);

  assert(nodesFound <= specialList.size());

  if (nodesFound < specialList.size()) return false;

  MDSpecialChildrenHelper *helper = NULL;
  switch (node->getKind()) {
  case ParallelMD::REGION:
    helper = static_cast<MDSpecialChildrenHelper *>(cast<RegionMD>(node));
    break;

  case ParallelMD::TASK:
    helper = static_cast<MDSpecialChildrenHelper *>(cast<TaskMD>(node));
    break;

  default:
    llvm_unreachable("Parent node not of correct type.");
  }

  for (unsigned i = beginIdx; i < rawNode->getNumOperands(); i++) {
    MDNode *rawChildNode = dyn_cast<MDNode>(rawNode->getOperand(i));
    assert(rawChildNode != NULL && "we have already checked for null "
           "child nodes");

    ParallelMD *childNode = createParallelMD(rawChildNode);
    if (childNode == NULL) return false;
    if (GetParentIfPossible(childNode) != node) return false;
    helper->children.push_back(childNode);
  }

  return true;
}


RegionMD *ParallelizationMetadata::createRegionMD(MDNode *node) {
  // !{ metadata !"region", functionBody, [ list of nested special regions ] }

  const unsigned bodyIdx = 1, nestedBeginIdx = 2, minMDLength = 2;

  RegionMD *region = NULL;
  Function *body = NULL;

  assert(node->getNumOperands() >= minMDLength &&
         "mangled !region metadata node");

  body = dyn_cast_or_null<Function>(node->getOperand(bodyIdx));
  if (body == NULL) goto failure;

  // See comment on addSpecialRegions
  region = new(allocator) RegionMD;
  (*rawNodeMap)[node] = region;

  // Check the consistency of the list of special-handling regions inside this
  // parallel region.

  if (!addSpecialRegions(region, node, body, nestedBeginIdx)) goto failure;

  region->body = body;
  return region;

  failure:
  (*rawNodeMap)[node] = NULL;
  return NULL;
}


SerialMD *ParallelizationMetadata::createSerialMD(MDNode *node) {
  // !{ metadata !"serial", functionBody, parentMetadata, ( !"master" | !"any" )

  const unsigned bodyIdx = 1, parentIdx = 2, tagIdx = 3, mdLength = 4;

  SerialMD *serial = NULL;
  Function *body = NULL;
  MDNode *parentMD = NULL;
  ParallelMD *parentPMD = NULL;
  SerialMD::Kind kind = SerialMD::ANY;

  assert(node->getNumOperands() == mdLength && "mangled !serial metadata node");

  body = dyn_cast_or_null<Function>(node->getOperand(bodyIdx));
  if (body == NULL) goto failure;

  serial = new(allocator) SerialMD;
  (*rawNodeMap)[node] = serial;

  parentMD = dyn_cast_or_null<MDNode>(node->getOperand(parentIdx));
  if (parentMD == NULL) goto failure;
  parentPMD = dyn_cast_or_null<ParallelMD>(createParallelMD(parentMD));
  if (parentPMD == NULL) goto failure;

  {
    MDString *str = dyn_cast_or_null<MDString>(node->getOperand(tagIdx));
    if (str == NULL) goto failure;

    static const StringRef masterTag = "master", anyTag = "any";

    if (str->getString() == masterTag) {
      kind = SerialMD::MASTER;
    } else if (str->getString() == anyTag) {
      kind = SerialMD::ANY;
    } else {
      goto failure;
    }
  }

  serial->body = body;
  serial->parent = parentPMD;
  serial->kind = kind;
  return serial;

  failure:
  (*rawNodeMap)[node] = NULL;
  return NULL;
}


CriticalMD *ParallelizationMetadata::createCriticalMD(MDNode *node) {
  // !{ metadata !"critical", functionBody, parentMetadata, !"tag" }
  const unsigned bodyIdx = 1, parentIdx = 2, tagIdx = 3, mdLength = 4;

  CriticalMD *critical = NULL;
  Function *body = NULL;
  MDNode *parentMD = NULL;
  ParallelMD *parentPMD = NULL;
  MDString *tagString = NULL;

  assert(node->getNumOperands() == mdLength &&
         "malformed !critical metadata node");

  body = dyn_cast_or_null<Function>(node->getOperand(bodyIdx));
  if (body == NULL) goto failure;

  critical = new(allocator) CriticalMD;
  (*rawNodeMap)[node] = critical;

  parentMD = dyn_cast_or_null<MDNode>(node->getOperand(parentIdx));
  if (parentMD == NULL) goto failure;
  parentPMD = dyn_cast_or_null<ParallelMD>(createParallelMD(parentMD));
  if (parentPMD == NULL) goto failure;

  tagString = dyn_cast_or_null<MDString>(node->getOperand(tagIdx));
  if (tagString == NULL) goto failure;

  critical->body = body;
  critical->parent = parentPMD;
  critical->tag = tagString->getString();
  return critical;

  failure:
  (*rawNodeMap)[node] = NULL;
  return NULL;
}

OrderedMD *ParallelizationMetadata::createOrderedMD(MDNode *node) {
  /// !{ metadata !"ordered", functionBody, parentLoopMetadata }
  const unsigned bodyIdx = 1, parentIdx = 2, mdLength = 3;

  OrderedMD *ordered = NULL;
  Function *body = NULL;
  MDNode *parentMD = NULL;
  LoopMD *parentLoopPMD = NULL;

  assert(node->getNumOperands() == mdLength && "mangled !ordered metdata node");

  body = dyn_cast_or_null<Function>(node->getOperand(bodyIdx));
  if (body == NULL) goto failure;

  ordered = new(allocator) OrderedMD;
  (*rawNodeMap)[node] = ordered;

  parentMD = dyn_cast_or_null<MDNode>(node->getOperand(parentIdx));
  if (parentMD == NULL) goto failure;
  parentLoopPMD = dyn_cast_or_null<LoopMD>(createParallelMD(parentMD));
  if (parentLoopPMD == NULL) goto failure;

  ordered->body = body;
  ordered->parent = parentLoopPMD;
  return ordered;

  failure:
  (*rawNodeMap)[node] = NULL;
  return NULL;
}


LoopMD *ParallelizationMetadata::createLoopMD(MDNode *node) {
  // !{ metadata !"loop", parentRegionMetadata, ( !"static" | !"guided" |
  //             !"dynamic" | !"runtime" | !"auto" ) integerLevel

  const unsigned parentIdx = 1, schedulingIdx = 2, levelsIdx = 3, mdLength = 3;

  assert (node->getNumOperands() == mdLength && "mangled !loop metadata node");

  LoopMD *loop = NULL;
  MDNode *parentMD = NULL;
  RegionMD *parentPMD = NULL;
  LoopMD::Schedule schedule = LoopMD::AUTO;
  int levels = 1;

  parentMD = dyn_cast_or_null<MDNode>(node->getOperand(parentIdx));
  if (parentMD == NULL) goto failure;

  loop = new(allocator) LoopMD;
  (*rawNodeMap)[node] = loop;

  parentPMD = dyn_cast_or_null<RegionMD>(createParallelMD(parentMD));
  if (parentPMD == NULL) goto failure;
  loop->parent = parentPMD;

  {
    static const StringRef staticTag = "static", dynamicTag = "dynamic",
      guidedTag = "guided", runtimeTag = "runtime", autoTag = "auto";

    MDString *string = dyn_cast<MDString>(node->getOperand(schedulingIdx));
    if (string == NULL) goto failure;

    StringRef tag = string->getString();
    if (tag == staticTag) {
      schedule = LoopMD::STATIC;
    } else if (tag == dynamicTag) {
      schedule = LoopMD::DYNAMIC;
    } else if (tag == guidedTag) {
      schedule = LoopMD::GUIDED;
    } else if (tag == runtimeTag) {
      schedule = LoopMD::RUNTIME;
    } else if (tag == autoTag) {
      schedule = LoopMD::AUTO;
    } else {
      goto failure;
    }
  }

  {
    MDString *levelString =
      dyn_cast_or_null<MDString>(node->getOperand(levelsIdx));
    if (levelString == NULL) goto failure;

    int result = ::sscanf(levelString->begin(), "%d", &levels);
    if (result != 1) goto failure;
  }

  loop->parent = parentPMD;
  loop->schedule = schedule;
  loop->levels = levels;
  return loop;

  failure:
  (*rawNodeMap)[node] = NULL;
  return NULL;
}


TaskMD *ParallelizationMetadata::createTaskMD(MDNode *node) {
  // !{ metdata !"task", functionBody, parentMetadata, ( !"untied" | !"tied" ),
  //            [ list of nested special regions ]

  const unsigned bodyIdx = 1, parentIdx = 2, affinityIdx = 3,
    nestedBeginIdx = 4, minMDLength = 4;
  assert(node->getNumOperands() > minMDLength &&
         "malformed !task metadata node");

  TaskMD *task = NULL;
  MDNode *parentMD = NULL;
  RegionMD *parentPMD = NULL;
  Function *body = NULL;
  TaskMD::Affinity affinity = TaskMD::UNTIED;

  body = dyn_cast_or_null<Function>(node->getOperand(bodyIdx));
  if (body == NULL) goto failure;

  parentMD = dyn_cast_or_null<MDNode>(node->getOperand(parentIdx));
  if (parentMD == NULL) goto failure;

  task = new(allocator) TaskMD;
  (*rawNodeMap)[node] = task;

  parentPMD = dyn_cast_or_null<RegionMD>(createParallelMD(parentMD));
  if (parentPMD == NULL) goto failure;

  {
    static const StringRef tiedTag = "tied", untiedTag = "untied";
    MDString *affString =
      dyn_cast_or_null<MDString>(node->getOperand(affinityIdx));

    if (affString == NULL) goto failure;

    if (affString->getString() == tiedTag) {
      affinity = TaskMD::TIED;
    } else if (affString->getString() == untiedTag) {
      affinity = TaskMD::UNTIED;
    } else {
      goto failure;
    }
  }

  if (!addSpecialRegions(task, node, body, nestedBeginIdx)) goto failure;

  task->parent = parentPMD;
  task->body = body;
  task->affinity = affinity;
  return task;

  failure:
  (*rawNodeMap)[node] = task;
  return task;
}


void ParallelizationMetadata::getAnalysisUsage(AnalysisUsage &AU) {
  AU.setPreservesAll();
}


ParallelMD *ParallelizationMetadata::createParallelMD(MDNode *node) {
  DenseMap<MDNode *, ParallelMD *>::iterator it = rawNodeMap->find(node);
  if (it != rawNodeMap->end()) return it->second;

  ParallelMD::MDKind kind = GetNodeKind(node);

  switch (kind) {
  case ParallelMD::REGION: return createRegionMD(node);
  case ParallelMD::SERIAL: return createSerialMD(node);
  case ParallelMD::CRITICAL: return createCriticalMD(node);
  case ParallelMD::ORDERED: return createOrderedMD(node);
  case ParallelMD::LOOP: return createLoopMD(node);
  case ParallelMD::TASK: return createTaskMD(node);
  case ParallelMD::MD_KIND_MAX: return NULL;
  default: llvm_unreachable("GetNodeKind returned absurd value");
  }
}


bool ParallelizationMetadata::runOnModule(Module &module) {
  StringRef tag = "parallel";
  DenseMap<MDNode *, ParallelMD *> rawNodeMapOnStack;
  rawNodeMap = &rawNodeMapOnStack;

  for (Module::const_iterator FI = module.begin(), FE = module.end();
       FI != FE; ++FI) {
    for (Function::const_iterator BI = FI->begin(), BE = FI->end();
         BI != BE; ++BI) {
      for (BasicBlock::const_iterator I = BI->begin(), E = BI->end();
           I != E; ++I) {
        MDNode *rawNode = I->getMetadata(tag);
        if (ParallelMD *node = createParallelMD(rawNode))
          instructionMap[I] = node;
      }
    }
  }

  rawNodeMap = NULL;
  return false;
}
