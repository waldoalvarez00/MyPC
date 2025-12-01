#!/usr/bin/env bash
set -euo pipefail

# Run all formal harnesses using temporary workdirs (-t),
# so no SymbiYosys artifacts are left on disk.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${REPO_ROOT}"

echo "Running DMAArbiter formal..."
sby -t -f formal/DMAArbiter.sby

echo "Running IDArbiter formal..."
sby -t -f formal/IDArbiter.sby

echo "Running MemArbiterExtend formal..."
sby -t -f formal/MemArbiterExtend.sby

echo "Running PipelinedDMAArbiter formal..."
sby -t -f formal/PipelinedDMAArbiter.sby

echo "Running PipelinedDMAFPUArbiter formal..."
sby -t -f formal/PipelinedDMAFPUArbiter.sby

echo "Running PipelinedMemArbiterExtend formal..."
sby -t -f formal/PipelinedMemArbiterExtend.sby

echo "Running ICache2Way formal..."
sby -t -f formal/ICache2Way.sby

echo "Running ICache2Way invalidation formal..."
sby -t -f formal/ICache2Way_inval.sby

echo "Running DCache2Way formal..."
sby -t -f formal/DCache2Way.sby

echo "Running CacheArbiter formal..."
sby -t -f formal/CacheArbiter.sby

echo "Running DCacheFrontendArbiter formal..."
sby -t -f formal/DCacheFrontendArbiter.sby

echo "Running Microcode formal..."
sby -t -f formal/Microcode.sby

echo "Running LoadStore formal..."
sby -t -f formal/LoadStore.sby

echo "Running MemArbiter formal..."
sby -t -f formal/MemArbiter.sby

echo "Running Prefetch formal..."
sby -t -f formal/Prefetch.sby

echo "Running Flags formal..."
sby -t -f formal/Flags.sby

echo "Running RegisterFile formal..."
sby -t -f formal/RegisterFile.sby

echo "Running FPU_Instruction_Queue formal..."
sby -t -f formal/FPU_Instruction_Queue.sby

echo "Running FPU_RegisterStack formal..."
sby -t -f formal/FPU_RegisterStack.sby

echo "Running FPU_Exception_Handler formal..."
sby -t -f formal/FPU_Exception_Handler.sby

echo "Running FPU_CPU_Interface formal..."
sby -t -f formal/FPU_CPU_Interface.sby

echo "Running FPU_IEEE754_AddSub formal..."
sby -t -f formal/FPU_IEEE754_AddSub.sby

echo "Running FPU_IEEE754_MulDiv_Unified formal..."
sby -t -f formal/FPU_IEEE754_MulDiv_Unified.sby

echo "Running FPU_SQRT_Newton formal..."
sby -t -f formal/FPU_SQRT_Newton.sby

echo "Running FPU_Format_Converter_Unified formal..."
sby -t -f formal/FPU_Format_Converter_Unified.sby

echo "Running FPU_Range_Reduction formal..."
sby -t -f formal/FPU_Range_Reduction.sby

echo "Running FPU_Polynomial_Evaluator formal..."
sby -t -f formal/FPU_Polynomial_Evaluator.sby

echo "All formal runs completed."
