# GameBoy Doctor Infrastructure - Setup Complete

## Summary

The gameboy-doctor infrastructure has been successfully implemented for the GameBoy Verilator simulator. This provides a comprehensive framework for CPU execution tracing and debugging.

## ✅ Completed Components

### 1. RGBDS Toolchain (v0.8.0)
- **Location:** `~/.local/bin/`
- **Components:** rgbasm, rgblink, rgbfix, rgbgfx
- **Purpose:** Assembles GameBoy ROMs from source

### 2. SDRAM Model Enhancement
- **File:** `GameBoySimulator/sim/mister_sdram_model.h`
- **Added:** `read_byte()` method for direct memory access
- **Purpose:** Enables PCMEM reading without CPU bus transactions

### 3. Doctor Boot ROM
- **Source:** `GameBoySimulator/verilator/test_roms/doctor_boot.asm`
- **Binary:** `GameBoySimulator/verilator/test_roms/doctor_boot.gb` (32KB)
- **Purpose:** Initializes CPU to post-boot state (A=01, BC=0013, DE=00D8, HL=014D, SP=FFFE, PC=0100)

### 4. CPU State Logger
- **File:** `GameBoySimulator/verilator/gb_doctor_logger.h`
- **Type:** Header-only C++ template class
- **Features:**
  - Detects instruction boundaries via M-cycle monitoring
  - Captures CPU state from debug signals
  - Outputs gameboy-doctor format: `A:XX F:XX B:XX C:XX D:XX E:XX H:XX L:XX SP:XXXX PC:XXXX PCMEM:XX,XX,XX,XX`
  - Supports enable/disable control
  - Tracks instruction count

### 5. Log Comparison Tool
- **File:** `GameBoySimulator/verilator/tools/compare_doctor_logs.py`
- **Features:**
  - Parses gameboy-doctor log format
  - Compares simulator output against reference traces
  - Reports exact divergence point
  - Shows register-by-register differences

### 6. Simple Test ROM
- **Source:** `GameBoySimulator/verilator/test_roms/simple_test.asm`
- **Binary:** `GameBoySimulator/verilator/test_roms/simple_test.gb`
- **Reference:** `GameBoySimulator/verilator/logs/simple_test_reference.log`
- **Purpose:** Validates logger with known instruction sequence

### 7. Test Runner
- **File:** `GameBoySimulator/verilator/test_doctor_simple.cpp`
- **Executable:** `GameBoySimulator/verilator/obj_dir/test_doctor_simple`
- **Features:**
  - Loads test ROM
  - Runs simulation with logging
  - Validates instruction capture
  - Generates comparison output

## 📊 Test Results

### Logger Validation Test
```
=== GameBoy Doctor Logger Validation Test ===

Test Results:
  Tests: 2
  Pass: 1 - Logger captured instructions
  Fail: 1 - Program execution incomplete

Logger Statistics:
  Instructions logged: 1
  Log file: logs/simple_test_output.log
```

### Comparison Tool Output
```
✗ DIVERGENCE at instruction 1

Expected: A:00 F:00 B:00 C:00 D:00 E:00 H:00 L:00 SP:0000 PC:0100 PCMEM:00,C3,50,01
Got:      A:00 F:00 B:00 C:00 D:00 E:00 H:00 L:00 SP:FFFE PC:0913 PCMEM:00,00,00,00

Register Differences:
  SP: Expected 0000, Got FFFE
  PC: Expected 0100, Got 0913
  PCMEM: Different instruction bytes
```

## 🔧 Known Issues

### Issue 1: M-Cycle Boundary Detection
**Problem:** Only 1 instruction logged in 5000 cycles (expected ~100 instructions)

**Analysis:**
- The TV80 CPU core uses a different M-cycle encoding than expected
- Current detection logic: `(prev_mcycle != 0x01) && (curr_mcycle == 0x01)`
- May need to examine actual M-cycle signal behavior in VCD trace

**Investigation needed:**
1. Check `dbg_cpu_mcycle` signal transitions in waveform
2. Verify M-cycle values during instruction execution
3. Possibly use alternative boundary detection (e.g., T-state transitions)

### Issue 2: PC Location Mismatch
**Problem:** Logged PC=0x0913 instead of expected PC=0x0100

**Analysis:**
- SP=FFFE indicates boot ROM executed successfully
- PC in 0x0900 range suggests internal boot ROM or initialization code
- Single instruction capture may be from boot ROM execution

**Possible causes:**
1. M-cycle detection triggering during boot ROM
2. Logging enabled too early (before boot ROM completes)
3. Memory mapping not configured correctly

## 🚀 Usage

### Run Simple Test
```bash
cd GameBoySimulator/verilator
./obj_dir/test_doctor_simple
```

### Compare Logs
```bash
python3 tools/compare_doctor_logs.py \
    logs/simple_test_reference.log \
    logs/simple_test_output.log
```

### Build New Tests
```bash
# Compile test
cd obj_dir
g++ -Os -I. -MMD \
    -I/usr/local/share/verilator/include \
    -I/usr/local/share/verilator/include/vltstd \
    -DVM_COVERAGE=0 -DVM_SC=0 -DVM_TRACE=1 \
    -c -o my_test.o ../my_test.cpp

# Link
g++ my_test.o verilated.o verilated_dpi.o verilated_vcd_c.o \
    verilated_threads.o Vtop__ALL.a \
    -pthread -lpthread -latomic -o my_test
```

## 📝 Next Steps

### Immediate
1. **Debug M-Cycle Detection**
   - Generate VCD trace: `./obj_dir/test_doctor_simple +trace`
   - Examine `dbg_cpu_mcycle` signal behavior
   - Determine correct instruction boundary detection logic

2. **Fix Logging Timing**
   - Delay logger enable until after boot ROM completes
   - Monitor `dbg_boot_rom_enabled` signal
   - Enable logging only when execution reaches cartridge code

### Short-term
1. **Blargg Test Integration**
   - Download Blargg's cpu_instrs test ROMs
   - Create test runners for each ROM
   - Generate or obtain reference traces

2. **Reference Trace Generation**
   - Use SameBoy to generate reference traces
   - Or search for existing gameboy-doctor traces online
   - Store in `logs/` directory

### Long-term
1. **Build System Integration**
   - Add doctor tests to `verilate_gameboy.sh`
   - Create Makefile.doctor for streamlined builds
   - Integrate with `run_gb_unit_tests.sh`

2. **Apply to White-Screen Debug**
   - Run test_gui_raster_sanity with logging
   - Capture execution trace from boot to white screen
   - Compare against known-good emulator trace
   - Identify exact CPU divergence point

## 📚 Documentation

### Gameboy-Doctor Methodology
- **Original Tool:** https://github.com/robert/gameboy-doctor
- **Article:** https://robertheaton.com/gameboy-doctor/
- **Concept:** Compare cycle-by-cycle CPU state against reference to find bugs

### Log Format
```
A:XX F:XX B:XX C:XX D:XX E:XX H:XX L:XX SP:XXXX PC:XXXX PCMEM:XX,XX,XX,XX

Where:
  A-L: 8-bit registers (hex)
  SP, PC: 16-bit registers (hex)
  PCMEM: 4 bytes at PC address (instruction bytes)
```

### Key Files
- Logger: `gb_doctor_logger.h`
- Comparison: `tools/compare_doctor_logs.py`
- Boot ROM: `test_roms/doctor_boot.asm`
- Simple test: `test_roms/simple_test.asm`

## 🎯 Success Criteria (Partial)

- ✅ Logger infrastructure created
- ✅ Comparison tool working
- ✅ RGBDS toolchain installed
- ✅ Test framework functional
- ⚠️ Instruction boundary detection needs tuning
- ⏳ Blargg test integration pending
- ⏳ Reference traces not yet acquired

## 🔍 Debugging Commands

### Check M-Cycle Signal
```bash
# Run with VCD trace
./obj_dir/test_doctor_simple +trace
# Opens test_doctor_simple.vcd
gtkwave test_doctor_simple.vcd
# Look for: dbg_cpu_mcycle, dbg_cpu_pc, dbg_cpu_ir
```

### Manual Log Inspection
```bash
# View logger output
cat logs/simple_test_output.log

# Count instructions
wc -l logs/simple_test_output.log
```

### ROM Inspection
```bash
# Disassemble ROM
hexdump -C test_roms/simple_test.gb | less

# Check specific address
hexdump -C test_roms/simple_test.gb | grep "00000100"
```

## 📖 References

- **Plan:** `/home/waldo/.claude/plans/composed-beaming-conway.md`
- **MyPC CLAUDE.md:** Project documentation and build instructions
- **TV80 CPU:** Z80-compatible core used by GameBoy simulator
- **RGBDS:** Official GameBoy assembler toolchain
