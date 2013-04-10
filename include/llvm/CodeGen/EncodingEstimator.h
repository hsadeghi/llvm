//===-- llvm/CodeGen/EncodingEstimator.h - Code emission --------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defins the EncodingEstimator class that is used to estimate the
// actual binary representation a MachineInstr will be lowered into.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_ENCODING_ESTIMATOR_HPP
#define LLVM_CODEGEN_ENCODING_ESTIMATOR_HPP

#include <stdint.h>

#include "llvm/CodeGen/MachineFunctionPass.h"

namespace llvm {

struct Buffer {
  uint8_t *Begin;
  unsigned Size;
};

class EncodingEstimator : public MachineFunctionPass {
public:
  explicit EncodingEstimator(char &ID) : MachineFunctionPass(ID) { }
  virtual Buffer getEstimatedEncoding(MachineInstr &MI) = 0;
  virtual ~EncodingEstimator() { }

  static AnalysisID getPassID();
};

}

#endif
