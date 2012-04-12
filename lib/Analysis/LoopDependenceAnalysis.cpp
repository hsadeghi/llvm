//===- LoopDependenceAnalysis.cpp - LDA Implementation ----------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is the (beginning) of an implementation of a loop dependence analysis
// framework, which is used to detect dependences in memory accesses in loops.
//
// Please note that this is work in progress and the interface is subject to
// change.
//
// TODO: adapt as implementation progresses.
//
// TODO: document lingo (pair, subscript, index)
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "lda"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopDependenceAnalysis.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Assembly/Writer.h"
#include "llvm/Instructions.h"
#include "llvm/Operator.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetData.h"
using namespace llvm;

STATISTIC(NumAnswered,    "Number of dependence queries answered");
STATISTIC(NumAnalysed,    "Number of distinct dependence pairs analysed");
STATISTIC(NumDependent,   "Number of pairs with dependent accesses");
STATISTIC(NumIndependent, "Number of pairs with independent accesses");

LoopPass *llvm::createLoopDependenceAnalysisPass() {
  return new LoopDependenceAnalysis();
}

INITIALIZE_PASS_BEGIN(LoopDependenceAnalysis, "lda",
                "Loop Dependence Analysis", false, true)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolution)
INITIALIZE_AG_DEPENDENCY(AliasAnalysis)
INITIALIZE_PASS_END(LoopDependenceAnalysis, "lda",
                "Loop Dependence Analysis", false, true)
char LoopDependenceAnalysis::ID = 0;

//===----------------------------------------------------------------------===//
//                             Utility Functions
//===----------------------------------------------------------------------===//

static inline bool IsMemRefInstr(const Value *V) {
  const Instruction *I = dyn_cast<const Instruction>(V);
  return I && (I->mayReadFromMemory() || I->mayWriteToMemory());
}

static void GetMemRefInstrs(const Loop *L,
                            SmallVectorImpl<Instruction*> &Memrefs) {
  for (Loop::block_iterator b = L->block_begin(), be = L->block_end();
       b != be; ++b)
    for (BasicBlock::iterator i = (*b)->begin(), ie = (*b)->end();
         i != ie; ++i)
      if (IsMemRefInstr(i))
        Memrefs.push_back(i);
}

static bool IsLoadOrStoreInst(Value *I) {
  // Returns true if the load or store can be analyzed. Atomic and volatile
  // operations have properties which this analysis does not understand.
  if (LoadInst *LI = dyn_cast<LoadInst>(I))
    return LI->isUnordered();
  else if (StoreInst *SI = dyn_cast<StoreInst>(I))
    return SI->isUnordered();
  return false;
}

static Value *GetPointerOperand(Value *I) {
  if (LoadInst *i = dyn_cast<LoadInst>(I))
    return i->getPointerOperand();
  if (StoreInst *i = dyn_cast<StoreInst>(I))
    return i->getPointerOperand();
  llvm_unreachable("Value is no load or store instruction!");
}

static AliasAnalysis::AliasResult UnderlyingObjectsAlias(AliasAnalysis *AA,
                                                         const Value *A,
                                                         const Value *B) {
  const Value *aObj = GetUnderlyingObject(A);
  const Value *bObj = GetUnderlyingObject(B);
  return AA->alias(aObj, AA->getTypeStoreSize(aObj->getType()),
                   bObj, AA->getTypeStoreSize(bObj->getType()));
}

static inline const SCEV *GetZeroSCEV(ScalarEvolution *SE) {
  return SE->getConstant(Type::getInt32Ty(SE->getContext()), 0L);
}

//===----------------------------------------------------------------------===//
//                             Dependence Testing
//===----------------------------------------------------------------------===//

bool LoopDependenceAnalysis::findOrInsertDependencePair(Value *A,
                                                        Value *B,
                                                        DependencePair *&P) {
  void *insertPos = 0;
  FoldingSetNodeID id;
  id.AddPointer(A);
  id.AddPointer(B);

  P = Pairs.FindNodeOrInsertPos(id, insertPos);
  if (P) return true;

  P = new (PairAllocator) DependencePair(id, A, B);
  Pairs.InsertNode(P, insertPos);
  return false;
}

void LoopDependenceAnalysis::getLoops(const SCEV *S,
                                      DenseSet<const Loop*>* Loops) const {
  // Refactor this into an SCEVVisitor, if efficiency becomes a concern.
  for (Loop *L = this->L; L != 0; L = L->getParentLoop())
    if (!SE->isLoopInvariant(S, L))
      Loops->insert(L);
}

bool LoopDependenceAnalysis::isLoopInvariant(const SCEV *S) const {
  DenseSet<const Loop*> loops;
  getLoops(S, &loops);
  return loops.empty();
}

bool LoopDependenceAnalysis::analyseZIV(const SCEV *A, const SCEV *B,
                                        Level *level, bool *dependent) const {
  DEBUG(dbgs() << "\t >> Analyzing ZIV { " << *A << ", " << *B <<  " }\n");
  if (isLoopInvariant(A) && isLoopInvariant(B)) {
    const SCEV *diffSCEV = SE->getMinusSCEV(A, B);
    if (SE->isKnownNonZero(diffSCEV)) {
      *dependent = false;
    } else {
      *dependent = true;
      level->direction = Level::ALL;
      level->distance = diffSCEV;
      level->scalar = true;
    }
    return true;
  }

  return false;
}

bool
LoopDependenceAnalysis::getLinearExpression(const SCEV *X, const SCEV **xCoeff,
                                            const SCEV **xConst,
                                            const Loop **loop) const {
  // We try to fill in xCoeff and xConst such that X = (*xConst) + (*xCoeff) * I
  // where I is the loop induction variable.
  if (const SCEVAddRecExpr *addRecExp = dyn_cast<SCEVAddRecExpr>(X)) {
    *xCoeff = addRecExp->getStepRecurrence(*SE);
    *xConst = addRecExp->getStart();
    *loop = addRecExp->getLoop();
    DEBUG(dbgs() << "\t >> Broke " << *X << " into " << **xCoeff << " and "
          << **xConst << "\n");
    return isLoopInvariant(*xConst) && isLoopInvariant(*xCoeff);
  } else if (isLoopInvariant(X)) {
    *xConst = X;
    *xCoeff = GetZeroSCEV(SE);
    *loop = NULL;
    return true;
  } else {
    DEBUG(dbgs() <<  "\t >> " << *X << " cannot be broken up!");
    return false;
  }
}

// Return true if the divisor divides the dividend without leaving a remainder.
static bool IsRemainderZero(const SCEVConstant *dividend,
                            const SCEVConstant *divisor) {
  APInt constDividend = dividend->getValue()->getValue();
  APInt constDivisor = divisor->getValue()->getValue();
  APInt quotient, remainder;
  APInt::sdivrem(constDividend, constDivisor, quotient, remainder);
  return remainder == 0;
}

bool LoopDependenceAnalysis::analyseStrongSIV(const SCEV *dstCoeff,
                                              const SCEV *dstConst,
                                              const SCEV *srcCoeff,
                                              const SCEV *srcConst,
                                              const Loop *loop,
                                              Level *level) const {
  DEBUG(dbgs() << "\t >> Analysing Strong SIV {" << *dstCoeff << " " <<
        *dstConst << " } { " << *srcCoeff << " " << *srcConst << " }\n");
  const SCEV *delta = SE->getMinusSCEV(dstConst, srcConst);
  // Check that |distance| < iteration count
  if (SE->hasLoopInvariantBackedgeTakenCount(loop)) {
    const SCEV *absDelta = SE->isKnownNonNegative(delta) ?
      delta : SE->getNegativeSCEV(delta);
    const SCEV *absCoeff = SE->isKnownNonNegative(srcCoeff) ?
      srcCoeff : SE->getNegativeSCEV(srcCoeff);
    const SCEV *iterationCount = SE->getBackedgeTakenCount(loop);
    const SCEV *product = SE->getMulExpr(iterationCount, absCoeff);
    const SCEV *conditionExpr = SE->getMinusSCEV(product, absDelta);
    if (SE->isKnownNegative(conditionExpr)) {
      // Independent
      return false;
    }
  }

  // Can we compute distance?
  if (isa<SCEVConstant>(delta) && isa<SCEVConstant>(srcCoeff)) {
    const SCEVConstant *constDelta = cast<SCEVConstant>(delta);
    const SCEVConstant *constCoeff = cast<SCEVConstant>(srcCoeff);
    APInt distance, remainder;
    APInt::sdivrem(constDelta->getValue()->getValue(),
                   constCoeff->getValue()->getValue(),
                   distance, remainder);
    if (remainder != 0) // Independent
      return false;
    level->distance = SE->getConstant(distance);
    if (distance.sgt(0))
      level->direction = Level::LT;
    else if (distance.slt(0))
      level->direction = Level::GT;
    else
      level->direction = Level::EQ;
  } else if (delta->isZero()) {
    // Since 0/X == 0
    level->distance = delta; // == 0
    level->direction = Level::EQ;
  } else {
    if (srcCoeff->isOne())
      level->distance = delta; // X/1 == X
    // Maybe we can get a useful direction vector
    bool deltaMaybeZero = !SE->isKnownNonZero(delta);
    bool deltaMaybePositive = !SE->isKnownNonPositive(delta);
    bool deltaMaybeNegative = !SE->isKnownNonNegative(delta);
    bool coeffMaybePositive = !SE->isKnownNonPositive(srcCoeff);
    bool coeffMaybeNegative = !SE->isKnownNonNegative(srcCoeff);
    level->direction = Level::NONE;
    if (deltaMaybeZero)
      level->direction |= Level::EQ;
    if ((deltaMaybeNegative && coeffMaybePositive) ||
        (deltaMaybePositive && coeffMaybeNegative))
      level->direction |= Level::GT;
    if ((deltaMaybePositive && coeffMaybePositive) ||
        (deltaMaybeNegative && coeffMaybeNegative))
      level->direction |= Level::LT;
  }

  // Could not prove independence
  return true;
}

bool LoopDependenceAnalysis::analyseWeakZeroSIV(const SCEV *destCoeff,
                                                const SCEV *destConst,
                                                const SCEV *srcCoeff,
                                                const SCEV *srcConst,
                                                const Loop *loop,
                                                Level *level) const {
  assert((destCoeff->isZero() || srcCoeff->isZero()) &&
         "For weak-zero one of the coefficients have to be zero!");
  DEBUG(dbgs() << "\t >> Analysing WeakZero SIV {" << *destCoeff << " " <<
        *destConst << " } { " << *srcCoeff << " " << *srcConst << " }\n");
  // Weak-zero test.
  // [ n0 = m * b + n1 ] => [ b = (n0 - n1) / m ]
  // [ m * a + n0 = n1 ] => [ a = (n1 - n0) / m ]
  const SCEV *distance = destCoeff->isZero() ?
    SE->getMinusSCEV(destConst, srcConst) : SE->getMinusSCEV(srcConst,
                                                             destConst);

  const SCEV *theCoeff = destCoeff->isZero() ? srcCoeff : destCoeff;
  if (SE->hasLoopInvariantBackedgeTakenCount(loop)) {
    const SCEV *iterationCount = SE->getBackedgeTakenCount(loop);
    const SCEV *conditionExpr =
      SE->getMinusSCEV(SE->getMulExpr(theCoeff, iterationCount), distance);
    if (SE->isKnownNonPositive(conditionExpr))
      return false;
  }

  if (isa<SCEVConstant>(distance) && isa<SCEVConstant>(theCoeff)) {
    if (!IsRemainderZero(cast<SCEVConstant>(distance),
                         cast<SCEVConstant>(theCoeff)))
      return false;
  }

  // Since we know at least one of the coefficients is zero, this falling under
  // weak-crossing-siv would mean that the pair is actually ZIV (which we know
  // is not the case).  Thus we know the pairs are dependent.
  level->direction = Level::ALL;
  level->scalar = true;
  return true;
}

bool LoopDependenceAnalysis::analyseWeakCrossingSIV(const SCEV *destCoeff,
                                                    const SCEV *destConst,
                                                    const SCEV *srcCoeff,
                                                    const SCEV *srcConst,
                                                    const Loop *loop,
                                                    Level *level) const {
  DEBUG(dbgs() << "\t >> Analysing WeakCrossing SIV {" << *destCoeff << " " <<
        *destConst << " } { " << *srcCoeff << " " << *srcConst << " }\n");
  // Weak-crossing test.
  // [ m * a + n0 = -m * b + n1 ] => [ a + b = (n1 - n0) / m ]

  // All (a, b) pairs are of the form (t - x, t + x) where t is ((n1 - n0) / 2
  // * m).  We check if t is of the form n / 2 where n is an integer, and if t
  // lies within the loop bounds.  This is because:
  //     t - x is integral, t + x is integral
  // => (t - x) + (t + x) is integral
  // =>  2 * t is integral.

  const SCEV *distance = SE->getMinusSCEV(srcConst, destConst);

  // First check the loop bounds.
  if (SE->hasLoopInvariantBackedgeTakenCount(loop)) {
    // (n1 - n0) / 2m <= L => (n1 - n0 - 2mL) <= 0
    const SCEV *iterationCount = SE->getBackedgeTakenCount(loop);
    const SCEV *constantTwo = SE->getConstant(iterationCount->getType(), 2);
    const SCEV *mL = SE->getMulExpr(destCoeff, iterationCount);
    const SCEV *conditionExpr =
      SE->getMinusSCEV(distance, SE->getMulExpr(constantTwo, mL));
    DEBUG(dbgs() << "\t >> Condition expression for weak-crossing: "
          << *conditionExpr << "\n");
    if (SE->isKnownNonPositive(conditionExpr))
      return false;
  }

  // Checking if t is of the form (n / 2, n is an integer) is equivalent to
  // checking (n1 - n0) / m is an integer.
  if (isa<SCEVConstant>(distance) && isa<SCEVConstant>(destCoeff)) {
    if (!IsRemainderZero(cast<SCEVConstant>(distance),
                         cast<SCEVConstant>(destCoeff)))
      return false;
  }

  level->direction = Level::ALL;
  level->scalar = true;
  return true;
}

bool LoopDependenceAnalysis::analyseSIV(const SCEV *dest, const SCEV *src,
                                        Level *level, bool *dependent) const {
  DEBUG(dbgs() << "\t >> SIV analysing " << *dest << ", " << *src << "\n");
  const SCEV *destCoeff, *destConst, *srcCoeff, *srcConst;
  const Loop *destLoop, *srcLoop, *loop;

  if (!getLinearExpression(dest, &destCoeff, &destConst, &destLoop) ||
      !getLinearExpression(src, &srcCoeff, &srcConst, &srcLoop))
    return false;

  DEBUG(dbgs() << "\t >> Broke A into " << *destCoeff << ", " <<
        *destConst << "\n");
  DEBUG(dbgs() << "\t >> Broke B into " << *srcCoeff << ", " <<
        *srcConst << "\n");

  loop = destLoop ? destLoop : srcLoop;
  assert(((loop == srcLoop) || (!srcLoop)) &&
         ((loop == destLoop) || (!srcLoop)) &&
         "Inconsistency in detecting loop in SIV!");

  if (destCoeff == srcCoeff)
    *dependent = analyseStrongSIV(destCoeff, destConst, srcCoeff, srcConst,
                                  loop, level);
  else if (destCoeff->isZero() || srcCoeff->isZero())
    *dependent = analyseWeakZeroSIV(destCoeff, destConst, srcCoeff, srcConst,
                                    loop, level);
  else if (destCoeff == SE->getNegativeSCEV(srcCoeff))
    *dependent = analyseWeakCrossingSIV(destCoeff, destConst, srcCoeff,
                                        srcConst, loop, level);
  else
    return false;

  return true;
}

// Return false on provable independence and true otherwise.  This convention is
// used in this source file wherever dependence needs to be represented by a
// bool.
bool LoopDependenceAnalysis::analyseSubscript(const SCEV *A,
                                              const SCEV *B,
                                              Level *level,
                                              const Loop **loop) const {
  DEBUG(dbgs() << "\t >> Testing subscript: " << *A << ", " << *B << "\n");

  bool dependent = false;
  *loop = NULL;
  if (const SCEVAddRecExpr *a = dyn_cast<SCEVAddRecExpr>(A))
    *loop = a->getLoop();
  if (const SCEVAddRecExpr *b = dyn_cast<SCEVAddRecExpr>(B)) {
    // TODO: This function signature assumes the subscripts aren't MIV (and
    // hence has only one Loop out parameter).
    if (*loop == NULL)
      *loop = b->getLoop();
    else if (*loop != b->getLoop())
      return true;
  }

  if (analyseZIV(A, B, level, &dependent))
    return dependent;

  if (analyseSIV(A, B, level, &dependent))
    return dependent;

  if (A == B) {
    DEBUG(dbgs() << "\t >> Same SCEV\n");
    level->direction = Level::EQ;
    return true;
  }

  return true;
}

void LoopDependenceAnalysis::Level::intersect(const Level &level) {
  direction &= level.direction;
  scalar = (scalar && level.scalar);
  distance = (distance == level.distance ? distance : NULL);
}

typedef SmallVector<const SCEV*, 4> GEPOpdsTy;

static const Loop *GetInnermostLoop(const GEPOpdsTy &indices) {
  const Loop *ret = NULL;
  for (GEPOpdsTy::const_iterator I = indices.begin(), E = indices.end();
       I != E; ++I) {
    if (const SCEVAddRecExpr *addRec = dyn_cast<SCEVAddRecExpr>(*I)) {
      const Loop *thisLoop = addRec->getLoop();
      if (ret == NULL || ret->contains(thisLoop))
        ret = thisLoop;
      else
        assert(thisLoop->contains(ret) && "");
    }
  }
  return ret;
}

LoopDependenceAnalysis::Dependence *
LoopDependenceAnalysis::analysePair(Value *dest, Value *src) const {
  DEBUG(dbgs() << "\t >> Analysing:\n" << *dest << "\n" << *src << "\n");

  // We only analyse loads and stores but no possible memory accesses by e.g.
  // free, call, or invoke instructions.
  if (!IsLoadOrStoreInst(dest) || !IsLoadOrStoreInst(src)) {
    DEBUG(dbgs() << "\t >> No load/store\n");
    return new Dependence(0);
  }

  Value *destPtr = GetPointerOperand(dest);
  Value *srcPtr = GetPointerOperand(src);

  switch (UnderlyingObjectsAlias(AA, destPtr, srcPtr)) {
  case AliasAnalysis::MayAlias:
  case AliasAnalysis::PartialAlias:
    // We can not analyse objects if we do not know about their aliasing.
    DEBUG(dbgs() << "\t >> May alias\n");
    return new Dependence(0);

  case AliasAnalysis::NoAlias: {
    // If the objects noalias, they are distinct, accesses are independent.
    DEBUG(dbgs() << "\t >> No alias\n");
    Dependence *d = new Dependence(0);
    d->result = Dependence::Independent;
    return d;
  }

  case AliasAnalysis::MustAlias:
    break; // The underlying objects alias, test accesses for dependence.
  }

  const GEPOperator *destGEP = dyn_cast<GEPOperator>(destPtr);
  const GEPOperator *srcGEP = dyn_cast<GEPOperator>(srcPtr);

  if (!destGEP || !srcGEP)
    return new Dependence(0);

  // Dividing subscripts into coupled and non-coupled groups might increase
  // preciseness.  Not doing so is, however, conservative and safe.

  // Collect GEP operand pairs (FIXME: use GetGEPOperands from BasicAA), adding
  // trailing zeroes to the smaller GEP, if needed.
  GEPOpdsTy destOpds, srcOpds;
  for(GEPOperator::const_op_iterator destIdx = destGEP->idx_begin(),
                                     destEnd = destGEP->idx_end(),
                                     srcIdx = srcGEP->idx_begin(),
                                     srcEnd = srcGEP->idx_end();
      destIdx != destEnd && srcIdx != srcEnd;
      destIdx += (destIdx != destEnd), srcIdx += (srcIdx != srcEnd)) {
    const SCEV* destSCEV = (destIdx != destEnd) ? SE->getSCEV(*destIdx) :
      GetZeroSCEV(SE);
    destOpds.push_back(destSCEV);
    const SCEV* srcSCEV = (srcIdx != srcEnd) ? SE->getSCEV(*srcIdx) :
      GetZeroSCEV(SE);
    srcOpds.push_back(srcSCEV);
  }

  if (destOpds.empty()) {
    Dependence *d = new Dependence(0);
    d->result = Dependence::Independent;
    return d;
  }

  // Even though we've established that the two pointers must alias, we can't
  // say much about the subscripts unless the types match.  This limitation can
  // be remedied by inspecting the structure of the types and multiplying the
  // subscripts by the sizes.
  if (destGEP->getPointerOperandType() != srcGEP->getPointerOperandType())
    return new Dependence(0);

  // Get the innermost loop the two Values live in and check if any one of them
  // contains the other.
  const Loop *destLoop = GetInnermostLoop(destOpds),
    *srcLoop = GetInnermostLoop(srcOpds),
    *loop = NULL;

  if (destLoop->contains(srcLoop)) {
    loop = destLoop;
  } else if (srcLoop->contains(destLoop)) {
    loop = srcLoop;
  } else {
    Dependence *d = new Dependence(0);
    d->result = Dependence::Dependent;
    return d;
  }

  Dependence *d = new Dependence(loop->getLoopDepth() + 1);
  Level subscriptInfo;
  // Now analyse the collected operand pairs (possibly skipping the GEP ptr
  // offsets).
  for (GEPOpdsTy::const_iterator destI = destOpds.begin(),
         destE = destOpds.end(), srcI = srcOpds.begin(), srcE = srcOpds.end();
       destI != destE; ++destI, ++srcI) {
    assert(srcI != srcE && "Subscript vectors differ in length!");
    const Loop *subscriptLoop = NULL;
    if (!analyseSubscript(*destI, *srcI, &subscriptInfo, &subscriptLoop)) {
      DEBUG(dbgs() << "\t >> Found independence!\n");
      d->result = Dependence::Independent;
      d->levels.clear();
      return d;
    } else {
      if (subscriptLoop)
        d->levels[subscriptLoop->getLoopDepth()].intersect(subscriptInfo);
    }
  }

  return d;
}

bool LoopDependenceAnalysis::isDependencePair(const Value *A,
                                              const Value *B) const {
  return IsMemRefInstr(A) &&
         IsMemRefInstr(B) &&
         (cast<const Instruction>(A)->mayWriteToMemory() ||
          cast<const Instruction>(B)->mayWriteToMemory());
}

LoopDependenceAnalysis::Dependence *
LoopDependenceAnalysis::depends(Value *destination, Value *source) {
  assert(isDependencePair(destination, source) &&
         "Values form no dependence pair (neither write to memory)!");
  ++NumAnswered;

  DependencePair *p;
  if (!findOrInsertDependencePair(destination, source, p)) {
    p->result = analysePair(destination, source);
    // The pair is not cached, so analyse it.
    ++NumAnalysed;
    switch (p->result->result) {
    case Dependence::Dependent:   ++NumDependent;   break;
    case Dependence::Independent: ++NumIndependent; break;
    }
  }

  return p->result;
}

//===----------------------------------------------------------------------===//
//                   LoopDependenceAnalysis Implementation
//===----------------------------------------------------------------------===//

bool LoopDependenceAnalysis::runOnLoop(Loop *L, LPPassManager &) {
  this->L = L;
  AA = &getAnalysis<AliasAnalysis>();
  SE = &getAnalysis<ScalarEvolution>();
  LI = &getAnalysis<LoopInfo>();
  return false;
}

void LoopDependenceAnalysis::releaseMemory() {
  Pairs.clear();
  PairAllocator.Reset();
}

void LoopDependenceAnalysis::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequiredTransitive<AliasAnalysis>();
  AU.addRequiredTransitive<ScalarEvolution>();
  AU.addRequiredTransitive<LoopInfo>();
}

static void PrintDependence(const LoopDependenceAnalysis::Dependence *dep,
                            raw_ostream &OS) {
  OS << (dep->getResult() ==
         LoopDependenceAnalysis::Dependence::Independent ? "I":"D") << " { ";
  for (LoopDependenceAnalysis::Dependence::const_iterator I =
         dep->begin(),E = dep->end(); I != E; ++I) {
    OS << "[ ";
    if (I->scalar)
      OS << "S ";

    if (I->direction & LoopDependenceAnalysis::Level::LT)
      OS << "<";
    if (I->direction & LoopDependenceAnalysis::Level::EQ)
      OS << "=";
    if (I->direction & LoopDependenceAnalysis::Level::GT)
      OS << ">";
    OS << " ";

    if (I->distance)
      OS << *(I->distance) << " ";
    OS << "] ";
  }
  OS << "}";
}

static void PrintLoopInfo(raw_ostream &OS,
                          LoopDependenceAnalysis *LDA, const Loop *L) {
  if (!L->empty()) return; // ignore non-innermost loops

  SmallVector<Instruction*, 8> memrefs;
  GetMemRefInstrs(L, memrefs);

  OS << "Loop at depth " << L->getLoopDepth() << ", header block: ";
  WriteAsOperand(OS, L->getHeader(), false);
  OS << "\n";

  OS << "  Load/store instructions: " << memrefs.size() << "\n";
  for (SmallVector<Instruction*, 8>::const_iterator x = memrefs.begin(),
       end = memrefs.end(); x != end; ++x)
    OS << "\t" << (x - memrefs.begin()) << ": " << **x << "\n";

  OS << "  Pairwise dependence results:\n";
  for (SmallVector<Instruction*, 8>::const_iterator x = memrefs.begin(),
         end = memrefs.end(); x != end; ++x)
    for (SmallVector<Instruction*, 8>::const_iterator y = memrefs.begin();
         y != end; ++y)
      if (LDA->isDependencePair(*x, *y)) {
        OS << "\t" << (x - memrefs.begin()) << "," << (y - memrefs.begin())
           << ": ";
        const LoopDependenceAnalysis::Dependence *result = LDA->depends(*x, *y);
        PrintDependence(result, OS);
        OS << "\n";
      }
}

void LoopDependenceAnalysis::print(raw_ostream &OS, const Module*) const {
  // TODO: doc why const_cast is safe
  PrintLoopInfo(OS, const_cast<LoopDependenceAnalysis*>(this), this->L);
}
