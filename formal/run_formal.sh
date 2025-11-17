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

echo "All formal runs completed."
