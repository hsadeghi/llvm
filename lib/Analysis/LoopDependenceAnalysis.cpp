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
STATISTIC(NumUnknown,     "Number of pairs with unknown accesses");

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

bool LoopDependenceAnalysis::isDependencePair(const Value *A,
                                              const Value *B) const {
  return IsMemRefInstr(A) &&
         IsMemRefInstr(B) &&
         (cast<const Instruction>(A)->mayWriteToMemory() ||
          cast<const Instruction>(B)->mayWriteToMemory());
}

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
                                        Subscript *S) const {
  if (isLoopInvariant(A) && isLoopInvariant(B)) {
    if (A == B) {
      S->Kind = Subscript::Dependent;
      S->Direction = Subscript::EQ;
      S->Distance = GetZeroSCEV(SE);
    } else {
      S->Kind = Subscript::Independent;
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
    DEBUG(dbgs() << "Broke " << *X << " into " << **xCoeff << " and "
          << **xConst << "\n");
    return isLoopInvariant(*xConst) && isLoopInvariant(*xCoeff);
  } else if (isLoopInvariant(X)) {
    *xConst = X;
    *xCoeff = GetZeroSCEV(SE);
    *loop = NULL;
    return true;
  } else {
    DEBUG(dbgs() << *X << " cannot be broken up!");
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

static const SCEV *To64Bit(ScalarEvolution *SE, const SCEV *expr) {
  assert(expr->getType()->isIntegerTy() &&
         "To64Bit expects SCEV's with integer types.");
  const Type *ty = expr->getType();

  if (ty->getIntegerBitWidth() < 64) {
    Type *i64 = Type::getIntNTy(SE->getContext(), 64);
    return SE->getZeroExtendExpr(expr, i64);
  } else if (ty->getIntegerBitWidth() == 64) {
    return expr;
  } else {
    return NULL;
  }
}

void LoopDependenceAnalysis::analyseStrongSIV(const SCEV *aCoeff,
                                              const SCEV *aConst,
                                              const SCEV *bCoeff,
                                              const SCEV *bConst,
                                              const Loop *loop,
                                              Subscript *S) const {
  DEBUG(dbgs() << "Strong SIV\n");
  assert(aCoeff == bCoeff && "Strong SIV expects equal coeffs!");

  // We have a strong SIV subscript here.
  // [ m * a + n0 = m * b + n1 ] => [ (a - b) = (n1 - n0) / m ]
  const SCEV *distance = SE->getMinusSCEV(bConst, aConst);
  DEBUG(dbgs() << "Distance SCEV is " << *distance << "\n");
  bool isGT = SE->isKnownNonPositive(distance)  ||
    // It is sometimes easier to check for a non-negative value than for a
    // negative value.
    SE->isKnownNonNegative(SE->getNegativeSCEV(distance));

  if (isGT)
    distance = SE->getNegativeSCEV(distance);

  if (SE->hasLoopInvariantBackedgeTakenCount(loop)) {
    const SCEV* iterationCount = To64Bit(SE, SE->getBackedgeTakenCount(loop));
    const SCEV *conditionExpr =
      SE->getMinusSCEV(SE->getMulExpr(iterationCount, aCoeff), distance);
    DEBUG(dbgs() << "Condition expression for strong SIV: "
          << *conditionExpr << "\n");
    if (SE->isKnownNonPositive(conditionExpr)) {
      S->Kind = Subscript::Independent;
      return;
    }
  }

  // Use more exact information if available.
  if (isa<SCEVConstant>(distance) && isa<SCEVConstant>(aCoeff)) {
    if (!IsRemainderZero(cast<SCEVConstant>(distance),
                         cast<SCEVConstant>(aCoeff))) {
      // aCoeff does not divide distance and the difference between induction
      // variables in two iterations is always integral.
      S->Kind = Subscript::Independent;
      return;
    }
  }

  // Since aCoeff == bCoeff, weak-zero and weak-crossing are possible iff
  // aCoeff == bCoeff == 0.  That case is already handled in the ZIV so we
  // claim dependence, filling up direction and deltaValue along the way.

  S->Kind = Subscript::Dependent;

  if (distance->isZero())
    S->Direction = Subscript::EQ;
  else if (isGT)
    S->Direction = Subscript::GT;
  else
    S->Direction = Subscript::LT;

  S->Distance = distance;

  DEBUG(dbgs() << "Dependent with " << S->Direction << ", " <<
        *S->Distance << "\n");
  return;
}

void LoopDependenceAnalysis::analyseWeakZeroSIV(const SCEV *aCoeff,
                                                const SCEV *aConst,
                                                const SCEV *bCoeff,
                                                const SCEV *bConst,
                                                const Loop *loop,
                                                Subscript *S) const {
  assert((aCoeff->isZero() || bCoeff->isZero()) &&
         "For weak-zero one of the coefficients have to be zero!");

  // Weak-zero test.
  // [ n0 = m * b + n1 ] => [ b = (n0 - n1) / m ]
  // [ m * a + n0 = n1 ] => [ a = (n1 - n0) / m ]
  const SCEV *distance = aCoeff->isZero() ?
    SE->getMinusSCEV(aConst, bConst) : SE->getMinusSCEV(bConst, aConst);

  const SCEV *theCoeff = aCoeff->isZero() ? bCoeff : aCoeff;
  if (SE->hasLoopInvariantBackedgeTakenCount(loop)) {
    const SCEV *iterationCount = SE->getBackedgeTakenCount(loop);
    const SCEV *conditionExpr =
      SE->getMinusSCEV(SE->getMulExpr(theCoeff, iterationCount), distance);
    if (SE->isKnownNonPositive(conditionExpr)) {
      S->Kind = Subscript::Independent;
      return;
    }
  }

  if (isa<SCEVConstant>(distance) && isa<SCEVConstant>(theCoeff)) {
    if (!IsRemainderZero(cast<SCEVConstant>(distance),
                         cast<SCEVConstant>(theCoeff))) {
      S->Kind = Subscript::Independent;
      return;
    }
  }

  // Since we know at least one of the coefficients is zero, this falling under
  // weak-crossing-siv would mean that the pair is actually ZIV (which we know
  // is not the case).  Thus we know the pairs are dependent.
  S->Kind = Subscript::Dependent;
  S->Direction = Subscript::ALL;
  return;
}

void LoopDependenceAnalysis::analyseWeakCrossingSIV(const SCEV *aCoeff,
                                                    const SCEV *aConst,
                                                    const SCEV *bCoeff,
                                                    const SCEV *bConst,
                                                    const Loop *loop,
                                                    Subscript *S) const {
  // Weak-crossing test.
  // [ m * a + n0 = -m * b + n1 ] => [ a + b = (n1 - n0) / m ]

  // All (a, b) pairs are of the form (t - x, t + x) where t is ((n1 - n0) / 2
  // * m).  We check if t is of the form n / 2 where n is an integer, and if t
  // lies within the loop bounds.  This is because:
  //     t - x is integral, t + x is integral
  // => (t - x) + (t + x) is integral
  // =>  2 * t is integral.

  const SCEV *distance = SE->getMinusSCEV(bConst, aConst);

  // First check the loop bounds.
  if (SE->hasLoopInvariantBackedgeTakenCount(loop)) {
    // (n1 - n0) / 2m <= L => (n1 - n0 - 2mL) <= 0
    const SCEV *iterationCount = SE->getBackedgeTakenCount(loop);
    const SCEV *constantTwo = SE->getConstant(iterationCount->getType(), 2);
    const SCEV *mL = SE->getMulExpr(aCoeff, iterationCount);
    const SCEV *conditionExpr =
      SE->getMinusSCEV(distance, SE->getMulExpr(constantTwo, mL));
    DEBUG(dbgs() << "Condition expression for weak-crossing: "
          << *conditionExpr << "\n");
    if (SE->isKnownNonPositive(conditionExpr)) {
      S->Kind = Subscript::Independent;
      return;
    }
  }

  // Checking if t is of the form (n / 2, n is an integer) is equivalent to
  // checking (n1 - n0) / m is an integer.
  if (isa<SCEVConstant>(distance) && isa<SCEVConstant>(aCoeff)) {
    if (!IsRemainderZero(cast<SCEVConstant>(distance),
                         cast<SCEVConstant>(aCoeff))) {
      S->Kind = Subscript::Independent;
      return;
    }
  }

  S->Kind = Subscript::Dependent;
  S->Direction = Subscript::ALL;
  return;
}

LoopDependenceAnalysis::Dependence
LoopDependenceAnalysis::analyseSubscriptVector(SmallVector<Subscript,4> &
                                               S) const {
  Dependence D;
  D.Result = Dependence::Dependent;

  for (SmallVector<Subscript, 4>::const_iterator I = S.begin(), E = S.end();
       I != E; ++I) {
    if (I->Kind == Subscript::Independent) {
      D.Result = Dependence::Independent;
      break;
    } else if (I->Kind == Subscript::Dependent) {
      if (I->Direction & Subscript::LT) {
        D.Result = Dependence::Dependent;
        break;
      } if (I->Direction & Subscript::EQ)
        continue;

      assert(I->Direction == Subscript::GT && "Expected >!");
      D.Result = Dependence::Independent;
      break;
    } else {
      assert(I->Kind == Subscript::Unknown && "Unknown subscript kind!");
      D.Result = Dependence::Unknown;
      break;
    }
  }

  D.Subscripts = S;
  return D;
}

bool LoopDependenceAnalysis::analyseSIV(const SCEV *A, const SCEV *B,
                                        Subscript *S) const {
  DEBUG(dbgs() << "SIV analysing " << *A << ", " << *B << "\n");
  const SCEV *aCoeff, *aConst, *bCoeff, *bConst;
  const Loop *loopA, *loopB, *loop;

  if (!getLinearExpression(A, &aCoeff, &aConst, &loopA) ||
      !getLinearExpression(B, &bCoeff, &bConst, &loopB))
    return false;

  DEBUG(dbgs() << "Broke A into " << *aCoeff << ", " << *aConst << "\n");
  DEBUG(dbgs() << "Broke B into " << *bCoeff << ", " << *bConst << "\n");

  loop = loopA ? loopA : loopB;
  assert(((loop == loopA) || (!loopA)) && ((loop == loopB) || (!loopB)) &&
         "Inconsistency in detecting loop in SIV!");

  if (aCoeff == bCoeff)
    analyseStrongSIV(aCoeff, aConst, bCoeff, bConst, loop, S);
  else if (aCoeff->isZero() || bCoeff->isZero())
    analyseWeakZeroSIV(aCoeff, aConst, bCoeff, bConst, loop, S);
  else if (aCoeff == SE->getNegativeSCEV(bCoeff))
    analyseWeakCrossingSIV(aCoeff, aConst, bCoeff, bConst, loop, S);
  else
    return false;

  return true;
}

bool LoopDependenceAnalysis::analyseMIV(const SCEV *A,
                                        const SCEV *B,
                                        Subscript *S) const {
  return false;
}

LoopDependenceAnalysis::Subscript
LoopDependenceAnalysis::analyseSubscript(const SCEV *A,
                                         const SCEV *B) const {
  DEBUG(dbgs() << "Testing subscript: " << *A << ", " << *B << "\n");

  Subscript S;
  S.Distance = NULL;
  S.Direction = Subscript::ALL;
  S.Kind = Subscript::Unknown;

  if (A == B) {
    DEBUG(dbgs() << "Same SCEV\n");

    S.Kind = Subscript::Dependent;
    S.Direction = Subscript::EQ;
    S.Distance = GetZeroSCEV(SE);
    return S;
  }

  if (analyseZIV(A, B, &S))
    return S;

  if (analyseSIV(A, B, &S))
    return S;

  if (!analyseMIV(A, B, &S))
    S.Kind = Subscript::Unknown;

  return S;
}

LoopDependenceAnalysis::Dependence
LoopDependenceAnalysis::analysePair(Value *A, Value *B) const {
  DEBUG(dbgs() << "Analysing:\n" << *A << "\n" << *B << "\n");

  Dependence D;

  // We only analyse loads and stores but no possible memory accesses by e.g.
  // free, call, or invoke instructions.
  if (!IsLoadOrStoreInst(A) || !IsLoadOrStoreInst(B)) {
    DEBUG(dbgs() << "No load/store\n");
    D.Result = Dependence::Unknown;
    return D;
  }

  Value *aPtr = GetPointerOperand(A);
  Value *bPtr = GetPointerOperand(B);

  switch (UnderlyingObjectsAlias(AA, aPtr, bPtr)) {
  case AliasAnalysis::MayAlias:
  case AliasAnalysis::PartialAlias:
    // We can not analyse objects if we do not know about their aliasing.
    DEBUG(dbgs() << "May alias\n");
    D.Result = Dependence::Unknown;
    return D;

  case AliasAnalysis::NoAlias:
    // If the objects noalias, they are distinct, accesses are independent.
    DEBUG(dbgs() << "No alias\n");
    D.Result = Dependence::Independent;
    return D;

  case AliasAnalysis::MustAlias:
    break; // The underlying objects alias, test accesses for dependence.
  }

  const GEPOperator *aGEP = dyn_cast<GEPOperator>(aPtr);
  const GEPOperator *bGEP = dyn_cast<GEPOperator>(bPtr);

  if (!aGEP || !bGEP) {
    D.Result = Dependence::Unknown;
    return D;
  }

  // Dividing subscripts into coupled and non-coupled groups might increace
  // preciseness.  Not doing so is, however, conservative and safe.

  // Collect GEP operand pairs (FIXME: use GetGEPOperands from BasicAA), adding
  // trailing zeroes to the smaller GEP, if needed.
  typedef SmallVector<std::pair<const SCEV*, const SCEV*>, 4> GEPOpdPairsTy;
  GEPOpdPairsTy opds;
  for(GEPOperator::const_op_iterator aIdx = aGEP->idx_begin(),
                                     aEnd = aGEP->idx_end(),
                                     bIdx = bGEP->idx_begin(),
                                     bEnd = bGEP->idx_end();
      aIdx != aEnd && bIdx != bEnd;
      aIdx += (aIdx != aEnd), bIdx += (bIdx != bEnd)) {
    const SCEV* aSCEV = (aIdx != aEnd) ? SE->getSCEV(*aIdx) : GetZeroSCEV(SE);
    const SCEV* bSCEV = (bIdx != bEnd) ? SE->getSCEV(*bIdx) : GetZeroSCEV(SE);
    opds.push_back(std::make_pair(aSCEV, bSCEV));
  }

  if (opds.empty()) {
    D.Result = Dependence::Dependent;
    return D;
  }

  // Even though we've established that the two pointers must alias, we can't
  // say much about the subscripts unless the types match.  This limitation can
  // be remedied by inspecting the structure of the types and multiplying the
  // subscripts by the sizes.
  if (aGEP->getPointerOperandType() != bGEP->getPointerOperandType()) {
    D.Result = Dependence::Unknown;
    return D;
  }

  Dependence result;

  // Now analyse the collected operand pairs (possibly skipping the GEP ptr
  // offsets).
  for (GEPOpdPairsTy::const_iterator I = opds.begin(), E = opds.end();
       I != E; ++I) {
    Subscript S = analyseSubscript(I->first, I->second);
    result.Subscripts.push_back(S);
  }

  return analyseSubscriptVector(result.Subscripts);
}

LoopDependenceAnalysis::Dependence
LoopDependenceAnalysis::depends(Value *A, Value *B) {
  assert(isDependencePair(A, B) && "Values form no dependence pair!");
  ++NumAnswered;

  DependencePair *p;
  if (!findOrInsertDependencePair(A, B, p)) {
    p->Result = analysePair(A, B);
    // The pair is not cached, so analyse it.
    ++NumAnalysed;
    switch (p->Result.Result) {
    case Dependence::Dependent:   ++NumDependent;   break;
    case Dependence::Independent: ++NumIndependent; break;
    case Dependence::Unknown:     ++NumUnknown;     break;
    }
  }

  return p->Result;
}

//===----------------------------------------------------------------------===//
//                   LoopDependenceAnalysis Implementation
//===----------------------------------------------------------------------===//

bool LoopDependenceAnalysis::runOnLoop(Loop *L, LPPassManager &) {
  this->L = L;
  AA = &getAnalysis<AliasAnalysis>();
  SE = &getAnalysis<ScalarEvolution>();
  TD = getAnalysisIfAvailable<TargetData>();
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
}

static void PrintDependence(const LoopDependenceAnalysis::Dependence *dep,
                            raw_ostream &OS) {
  static const char * idxText = "IDU";
  OS << idxText[dep->Result] << " { ";
  for (SmallVector<LoopDependenceAnalysis::Subscript, 4>::const_iterator I =
         dep->Subscripts.begin(),
         E = dep->Subscripts.end(); I != E; ++I) {
    OS << "[ ";
    OS << idxText[I->Kind];

    if (I->Kind == LoopDependenceAnalysis::Subscript::Independent) {
      OS << " ]";
      continue;
    } else {
      OS << ", ";
    }

    if (I->Direction & LoopDependenceAnalysis::Subscript::LT)
      OS << "<";
    if (I->Direction & LoopDependenceAnalysis::Subscript::EQ)
      OS << "=";
    if (I->Direction & LoopDependenceAnalysis::Subscript::GT)
      OS << ">";
    OS << ", ";

    if (I->Distance)
      OS << *I->Distance << " ";
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
        LoopDependenceAnalysis::Dependence result = LDA->depends(*x, *y);
        PrintDependence(&result, OS);
        OS << "\n";
      }
}

void LoopDependenceAnalysis::print(raw_ostream &OS, const Module*) const {
  // TODO: doc why const_cast is safe
  PrintLoopInfo(OS, const_cast<LoopDependenceAnalysis*>(this), this->L);
}
