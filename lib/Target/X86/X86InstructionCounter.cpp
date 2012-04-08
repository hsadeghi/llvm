#include "llvm/Function.h"
#include "llvm/Pass.h"

#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineFunction.h"

#include "llvm/Target/TargetMachine.h"

#define DEBUG_TYPE "instruction-count"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include <cstdio>
#include <fstream>

using namespace llvm;
using namespace std;

#define MAX_LOOP_DEPTH 4

namespace {
class X86InstructionCounter : public MachineFunctionPass {
private:
  static char ID;
  const MachineLoopInfo *MLI;
  string OutputFile;
  ofstream outStream;

  struct {
    unsigned long numStores,
      numLoads, numBranches,
      numInstrs;
  } InstrInfo[MAX_LOOP_DEPTH + 1];

public:
  X86InstructionCounter(string opFile) : MachineFunctionPass(ID),
                                         OutputFile(opFile) {}

  void processMBB(const MachineBasicBlock &MBB) {
    unsigned depth = MLI->getLoopDepth(&MBB);
    if (depth > MAX_LOOP_DEPTH)
      depth = MAX_LOOP_DEPTH;

    for (MachineBasicBlock::const_iterator I = MBB.begin(), E = MBB.end();
         I != E; ++I) {
      InstrInfo[depth].numInstrs++;
      if (I->mayLoad())
        InstrInfo[depth].numLoads++;
      if (I->mayStore())
        InstrInfo[depth].numStores++;
      if (I->isBranch())
        InstrInfo[depth].numBranches++;
    }
  }

  bool runOnMachineFunction(MachineFunction &MF) {
    assert(!OutputFile.empty() && "Null file name!");
    DEBUG(dbgs() << "Writing to '" << OutputFile << "'\n");
    outStream.open(OutputFile.c_str(), ios::app);
    if (!outStream) {
      dbgs() << "Could not open file for writing!\n";
      return false;
    }

    MLI = &getAnalysis<MachineLoopInfo>();

    memset(&InstrInfo, 0, sizeof(InstrInfo));

    for (MachineFunction::const_iterator I = MF.begin(), E = MF.end();
         I != E; ++I)
      processMBB(*I);

    outStream << "***************************************************** \n";
    outStream << "In function `" << MF.getFunction()->getName().data()
              << "`: \n\n";

    for (int i = 0; i < (MAX_LOOP_DEPTH + 1); i++) {
      outStream << "For loop depth " << i << "\n";
      outStream << "\tInstructions = " << InstrInfo[i].numInstrs << "\n";
      outStream << "\tLoads = " << InstrInfo[i].numLoads << "\n";
      outStream << "\tStores = " << InstrInfo[i].numStores << "\n";
      outStream << "\tBranches = " << InstrInfo[i].numBranches << "\n";
      outStream << "\n";
    }
    outStream << "***************************************************** \n\n";
    outStream.close();
    return false;
  };

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesCFG();
    AU.addRequired<MachineLoopInfo>();
    MachineFunctionPass::getAnalysisUsage(AU);
  };

  bool doInitialization(Module &m) {
    remove(OutputFile.c_str());
    return MachineFunctionPass::doInitialization(m);
  }

};
}

namespace llvm {
FunctionPass *createX86InstructionCounterPass(string fileName) {
  return new X86InstructionCounter(fileName);
}
}

char X86InstructionCounter::ID = 0;
