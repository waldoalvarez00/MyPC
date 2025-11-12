# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

MyPC is a complete **80186 CPU + 8087 FPU** PC emulation for the MiSTer FPGA platform, featuring:
- Microcode-driven 80186 CPU with Harvard architecture caches
- Full IEEE 754-compliant 8087 FPU (165/165 tests passing)
- Complete VGA/MCGA/CGA/EGA graphics (15 video modes)
- Comprehensive peripheral support (8259 PIC, 8253 PIT, 8237 DMA, floppy, UART, PS/2)
- Targets MiSTer DE10-Nano (Intel Cyclone V FPGA)

**Key Architectural Concept:** This is a **microcode-driven** system where x86 instructions are implemented as microcode sequences. Both the CPU and FPU use separate microassemblers.

## Build Commands

### FPGA Synthesis (Quartus)
```bash
cd Quartus/
quartus_sh --flow compile mycore              # Full compile
quartus_fit mycore --report_level standard    # Place and route
quartus_sta mycore                            # Timing analysis
```

**Requirements:** Quartus 17.0.0 Lite Edition (for MiSTer compatibility)

**Output:** `mycore.rbf` (Raw Binary File for MiSTer loading)

### CPU Microcode Build
```bash
cd utils/microassembler/
python uasm.py -o ../../Quartus/rtl/CPU/InstructionDefinitions.sv microcode/*.us
```

**Rebuilds:**
- `InstructionDefinitions.sv` - Microcode ROM with 1,196 microinstructions
- `MicrocodeTypes.sv` - Type definitions

**Note:** Microcode changes require full FPGA rebuild.

### FPU Microcode Build
```bash
cd Quartus/rtl/FPU8087/
python microasm.py <input.us> -o <output.hex>
```

**Generates:** Hex files loaded by FPU microsequencer ROM

### Testing

**Run all tests:**
```bash
cd modelsim/
./run_all_tests.sh
```

**Run individual component tests:**
```bash
./run_cache_test.sh           # Cache tests
./run_pic_test.sh             # Interrupt controller
./run_timer_test.sh           # Timer/PIT
./run_dma_test.sh             # DMA controller
./run_floppy_sd_test.sh       # Floppy controller
./run_ps2_keyboard_test.sh    # PS/2 keyboard
./run_ps2_mouse_test.sh       # PS/2 mouse
./run_ppi_test.sh             # Programmable Peripheral Interface
```

**Run FPU tests:**
```bash
cd Quartus/rtl/FPU8087/
./run_all_tests.sh
```

**Test Framework:** Icarus Verilog (despite directory name "modelsim")

**Test Status:** 196/207 tests passing (95% success rate)

## Architecture Overview

### CPU Core (80186)
**Location:** `Quartus/rtl/CPU/`

**Critical Files:**
- `Core.sv` - Main CPU with Harvard architecture interfaces:
  - **Instruction bus:** 19-bit address, 16-bit data (read-only)
  - **Data bus:** 19-bit address, 16-bit data (read/write, byte-selectable)
- `Microcode.sv` - Microcode execution engine (1,196 microinstructions, 95-bit format)
- `LoadStore.sv` - Memory access unit (handles aligned/unaligned accesses, MMIO detection)
- `Prefetch.sv` - 6-byte instruction prefetch queue
- `Divider.sv` - Multi-cycle division unit (16-32 cycles)
- `alu/ALU.sv` - Arithmetic/Logic Unit

**Key Characteristic:** **Stall-driven architecture** - any component asserting `busy` (LoadStore, Divider, ALU) halts the entire microcode sequencer.

**Microcode Source:** `utils/microassembler/microcode/*.us` (59 files)
- Examples: `add.us`, `mov.us`, `jmp.us`, `int.us`, `esc.us` (FPU interface)
- Language: TextX-parsed microcode assembly with labels, conditionals, field assignments

### FPU Core (8087)
**Location:** `Quartus/rtl/FPU8087/`

**Status:** ✅ Complete implementation (100% - all 165 tests passing)

**Critical Files:**
- `FPU8087.v` - Top-level FPU integration
- `FPU_Core.v` (137K lines!) - Main execution engine with 8-register stack (ST(0)-ST(7))
- `FPU_CPU_Interface.v` - Coprocessor interface bridge (handles instruction decode, format conversion, FWAIT)
- `MicroSequencer_Extended_BCD.v` (47K lines) - Microcode engine

**Arithmetic Units:**
- `FPU_IEEE754_AddSub.v` - Add/subtract
- `FPU_IEEE754_MulDiv_Unified.v` - Shared multiplier/divider (19% area reduction)
- `FPU_SQRT_Newton.v` - Newton-Raphson square root
- `FPU_Transcendental.v` - SIN, COS, TAN, ATAN
- `FPU_CORDIC_Wrapper.v` - CORDIC algorithm for rotation

**Coprocessor Protocol:**
1. CPU detects ESC instruction (0xD8-0xDF)
2. FPU acknowledges and begins execution (`cpu_fpu_busy = 1`)
3. CPU stalls on FWAIT (0x9B) until FPU ready
4. Data transferred via dedicated interface (16/32/64/80-bit conversions)

### Cache System (Harvard Architecture - RECOMMENDED)
**Location:** `Quartus/rtl/common/`

**Current Implementation:**
- **ICache.sv** - 8 KB instruction cache (512 lines × 8 words, direct-mapped)
- **DCache.sv** - 8 KB data cache (512 lines × 8 words, write-through with dirty tracking)
- **HarvardArbiter.sv** - Priority arbiter (D-cache writes highest, round-robin reads)
- **HarvardCacheSystem.sv** - Top-level integration

**Performance:** +40-50% throughput vs unified cache (eliminates serialization bottleneck)

**Alternative:** `Cache.sv` - Original unified cache (requires IDArbiter serialization)

**Hit Latency:** 1-2 cycles | **Miss Latency:** 8-16 cycles (SDRAM line fill)

### Video Subsystem
**Location:** `Quartus/rtl/VGA/` and `Quartus/rtl/CGA/`

**Supported Modes:** 15/15 standard PC video modes (100% tested)
- CGA: 40×25, 80×25 text; 320×200 4-color, 640×200 2-color
- MDA: 80×25 mono text (720×350)
- EGA: 320×200, 640×200, 640×350 (16-color)
- VGA: 640×480 (2/16-color)
- MCGA: 320×200 256-color (Mode 13h)

**Key Files:**
- `VGAController.sv` - Main VGA timing and pixel generation
- `VGARegisters.sv` - CRTC register programming interface
- `FrameBuffer.sv` - Shared SDRAM framebuffer
- `cgacard.sv` - CGA compatibility layer
- `UM6845R.sv` - MC6845 CRTC emulation

### Peripherals
**Location:** `Quartus/rtl/KF8237-DMA/`, `KF8253/`, `KF8255/`, `KF8259/`, etc.

**Fully Functional (100% tested):**
- **KF8259** - 8259A PIC (17/17 tests)
- **KF8253** - 8253 PIT (15/15 tests)
- **KF8255** - 8255 PPI (17/17 tests)
- **KF8237-DMA** - DMA Controller (24/24 tests)
- **uart16750_sv** - UART with FIFO
- **Floppy/** - Floppy controller with SD backend (26/26 tests)
- **ps2/** - PS/2 keyboard (18/18) and mouse (14/14) controllers

## Common Development Tasks

### Adding a New CPU Instruction

1. Create `.us` file in `utils/microassembler/microcode/`
   ```
   microcode my_new_instruction {
       mar_write, mar_wr_sel EA;    // Address calculation
       mdr_write, mem_read;         // Memory read
       alu_op ADD, update_flags ARITH;
       next_instruction;            // End microprogram
   }
   ```

2. Rebuild microcode:
   ```bash
   cd utils/microassembler/
   python uasm.py -o ../../Quartus/rtl/CPU/InstructionDefinitions.sv microcode/*.us
   ```

3. Recompile in Quartus (full rebuild required)

### Modifying Cache Behavior

1. Edit `ICache.sv` or `DCache.sv` in `Quartus/rtl/common/`
2. Update `HarvardCacheSystem.sv` if interface changes
3. Test with `modelsim/harvard_cache_tb.sv`:
   ```bash
   cd modelsim/
   ./run_harvard_cache_test.sh
   ```
4. Verify FPGA timing still meets 50 MHz target

### Adding a New Peripheral

1. Create module in appropriate `rtl/` subdirectory
2. Add to address decoder in `Quartus/rtl/common/Top.sv`
3. Wire interrupt signals to KF8259 PIC if needed
4. Create testbench in `modelsim/<peripheral>_tb.sv`
5. Create test script `modelsim/run_<peripheral>_test.sh`
6. Add to `modelsim/run_all_tests.sh`

### Debugging Test Failures

1. Run individual test with verbose output
2. Check waveform files (`.vcd` format, view with GTKWave)
3. Review test log in `master_test_results_<timestamp>/`
4. Common issues:
   - **Timing:** Icarus Verilog is strict about non-blocking assignments
   - **Initialization:** Always reset signals properly (X propagation causes failures)
   - **ACK signals:** Registered vs. combinational timing matters

## Critical Integration Points

### CPU ↔ Cache Interface

**Harvard Architecture Buses:**

**Instruction Bus (Core.sv):**
```systemverilog
output logic [19:1] instr_m_addr,      // Byte address (1 MB space)
output logic        instr_m_access,    // Request valid
input  logic [15:0] instr_m_data_in,   // Instruction data
input  logic        instr_m_ack        // Cache ready
```

**Data Bus (Core.sv):**
```systemverilog
output logic [19:1] data_m_addr,
output logic        data_m_access,
output logic [15:0] data_m_data_out,
output logic        data_m_wr_en,
output logic [1:0]  data_m_bytesel,    // 11=word, 10=high byte, 01=low byte
input  logic [15:0] data_m_data_in,
input  logic        data_m_ack,
output logic        d_io               // I/O vs memory
```

**Critical Path:** CPU → ICache/DCache → HarvardArbiter → SDRAM Controller → Physical SDRAM

### CPU ↔ FPU Interface

**Protocol Phases:**
1. CPU detects ESC instruction (opcode 0xD8-0xDF range)
2. CPU sets `cpu_fpu_instr_valid = 1`, passes opcode and ModR/M byte
3. FPU acknowledges with `cpu_fpu_instr_ack` (one-cycle pulse)
4. If memory operand: CPU handles address calculation, provides data
5. FPU executes (`cpu_fpu_busy = 1`)
6. CPU FWAIT stalls until `cpu_fpu_ready = 1`
7. Results available via status word or stack

**Format Conversions (handled by FPU_CPU_Interface.v):**
- 16/32/64-bit integer ↔ 80-bit extended real
- 32-bit float, 64-bit double ↔ 80-bit extended real
- BCD ↔ 80-bit extended real

### Memory Arbitration

**Harvard Arbiter Priority (HarvardArbiter.sv):**
1. **Highest:** D-cache write operations (data consistency)
2. **Round-robin:** Simultaneous read requests (fair scheduling)
3. **Single:** Grant to sole requestor

**Conflict Rate:** Only ~2% of cycles have simultaneous cache misses

## Important Notes

### Microcode System
- **Two separate microassemblers** - CPU and FPU use different formats
- CPU: 95-bit microinstructions, 1,196 entries, TextX-parsed `.us` files
- FPU: 32-bit microinstructions, simpler format, Python-based assembler
- **Changes require full FPGA rebuild** - microcode is ROM, not runtime

### Timing and Performance
- **Target Clock:** 50 MHz (tight timing closure on Cyclone V)
- **FPGA Utilization:** ~78% ALMs (comfortable margin for MiSTer)
- **Critical Path:** Watch LoadStore unit and cache tag matching
- **Byte Addressing:** SystemVerilog uses bit addressing, x86 uses byte → `addr[19:1]` not `addr[19:0]`

### Testing Strategy
- **Always run regression tests** before committing: `./run_all_tests.sh`
- **Unit tests:** Individual component testbenches (192 for caches, 15 for timer, etc.)
- **Integration tests:** System-level (VGA, DMA+Floppy, PS/2, etc.)
- **FPGA validation:** Real hardware testing on MiSTer (final verification)

### Common Pitfalls
1. **Modifying files in Quartus IDE** - Manually edit `files.qip` or `.qsf` instead
2. **Microcode changes** - Must rebuild from `.us` sources, can't edit generated `.sv` directly
3. **Cache coherency** - Harvard caches need careful self-modifying code handling
4. **Signal initialization** - Always reset properly to avoid X propagation in simulation
5. **Enum ternary operators** - Icarus Verilog is strict; use if-else instead for portability

### File Organization
- **RTL sources:** `Quartus/rtl/` (organized by subsystem)
- **Testbenches:** `modelsim/*_tb.sv`
- **Test scripts:** `modelsim/run_*_test.sh`
- **Documentation:** `docs/` (99 detailed documents!)
- **CPU microcode:** `utils/microassembler/microcode/*.us`
- **FPU microcode:** `Quartus/rtl/FPU8087/*.us`
- **Build utilities:** `utils/microassembler/uasm.py`, `Quartus/rtl/FPU8087/microasm.py`

## Key Documentation Files

Essential reading for understanding specific subsystems:

- `README.md` - High-level project overview
- `docs/HARVARD_CACHE_ARCHITECTURE.md` - Modern cache design details
- `docs/CPU_ARCHITECTURE_BOTTLENECK_ANALYSIS.md` - Performance analysis
- `docs/TESTING_SUMMARY.md` - Complete test status and results
- `docs/CACHE_OPTIMIZATION_QUICK_REFERENCE.md` - Cache tuning guide
- `docs/FPU_*.md` - FPU implementation documentation (multiple files)
- `docs/VGA_MODES_IMPLEMENTATION.md` - Video mode implementation

## Git Workflow

**Main Branch:** `main`

**Current Status:**
- 80186 CPU: Production ready
- 8087 FPU: Complete (165/165 tests passing)
- Harvard Caches: Implemented, tested (192/192 tests passing)
- Video: All 15 modes implemented and tested
- Peripherals: 95% test pass rate

**Before Committing:**
1. Run `modelsim/run_all_tests.sh` (must maintain 95%+ pass rate)
2. Check FPGA utilization (must stay under 85% for MiSTer)
3. Verify timing closure at 50 MHz
4. Update relevant documentation in `docs/` if architectural changes

## FPGA Resource Constraints

**Target Platform:** Intel Cyclone V 5CSEBA6U23I7 (MiSTer DE10-Nano)

**Current Utilization:** ~78% ALMs (comfortable margin)

**Critical Resources:**
- ALMs (Adaptive Logic Modules): Watch FPU arithmetic units
- M10K RAM blocks: Used for caches, FIFOs, register files
- DSP blocks: Used for FPU multiplication

**Optimization Strategies:**
- FPU already optimized: Shared multiplier/divider (19% area reduction)
- Cache sizes tunable via parameters (currently 8 KB each)
- Peripheral count: All essential peripherals included
- quartus located at /c/intelFPGA_lite/17.0/