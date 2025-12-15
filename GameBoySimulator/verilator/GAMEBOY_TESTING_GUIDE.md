# GameBoy Simulator Testing Guide

This document explains how to run and debug the GameBoy simulator using Blargg test ROMs and the GameBoy Doctor tool.

## Directory Structure

```
GameBoySimulator/verilator/
├── test_blargg_serial          # Main Blargg test runner (serial output)
├── test_doctor_compare         # GameBoy Doctor comparison test
├── run_all_doctor_tests.sh     # Script to run all doctor tests
├── test_roms/
│   └── cpu_instrs/
│       └── individual/         # Blargg CPU instruction test ROMs
│           ├── 01-special.gb
│           ├── 02-interrupts.gb
│           ├── ...
│           └── 11-op a,(hl).gb
├── gameboy-doctor/
│   ├── gameboy-doctor          # Python comparison tool
│   └── truth/
│       ├── zipped/cpu_instrs/  # Compressed reference logs
│       └── unzipped/cpu_instrs/ # Extracted reference logs
├── logs/                       # Generated test logs
└── obj_dir/                    # Verilator build directory
```

## Test ROMs

| Test # | ROM File | Description |
|--------|----------|-------------|
| 1 | 01-special.gb | Special instructions (DAA, CPL, SCF, CCF) |
| 2 | 02-interrupts.gb | Interrupt handling (EI, DI, HALT, vectors) |
| 3 | 03-op sp,hl.gb | Stack pointer and HL operations |
| 4 | 04-op r,imm.gb | Register with immediate operand |
| 5 | 05-op rp.gb | Register pair operations |
| 6 | 06-ld r,r.gb | Register-to-register loads |
| 7 | 07-jr,jp,call,ret,rst.gb | Jump, call, return instructions |
| 8 | 08-misc instrs.gb | Miscellaneous instructions |
| 9 | 09-op r,r.gb | Register-to-register operations |
| 10 | 10-bit ops.gb | Bit manipulation (BIT, SET, RES) |
| 11 | 11-op a,(hl).gb | Accumulator with (HL) operations |

---

## Method 1: Blargg Serial Output Tests

These tests run the ROM and capture serial output. Tests print "Passed" or "Failed" when complete.

### Run a Single Test

```bash
cd /mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator

# Basic usage
./test_blargg_serial test_roms/cpu_instrs/individual/06-ld\ r,r.gb

# With timeout (recommended for long tests)
timeout 3600 ./test_blargg_serial test_roms/cpu_instrs/individual/03-op\ sp,hl.gb
```

### Expected Output

```
=== Blargg Test Runner with Serial Output ===
Loaded ROM: 32768 bytes
Initializing cart_ready...
cart_ready = 1
Running test (capturing serial output)...

Serial output:
----------------------------------------
06-ld r,r

Passed
[Test result found, stopping]
----------------------------------------
TEST PASSED!
```

### Test Timing

| Test | Approximate Cycles | Approximate Time |
|------|-------------------|------------------|
| 06-ld r,r | ~40M | ~2 minutes |
| 01-special | ~100M | ~5 minutes |
| 02-interrupts | ~500M+ | ~30+ minutes |
| 03-op sp,hl | ~800M+ | ~45+ minutes |
| 09-op r,r | ~1B+ | ~60+ minutes |

The test binary has a 2 billion cycle limit to accommodate long-running tests.

---

## Method 2: GameBoy Doctor Tests

GameBoy Doctor compares CPU state traces against known-good reference logs, showing exactly where emulation diverges.

### Prerequisites

1. **Unzip reference logs** (one-time setup):
```bash
cd /mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator
mkdir -p gameboy-doctor/truth/unzipped/cpu_instrs

for i in 1 2 3 4 5 6 7 8 9 10 11; do
    unzip -o "gameboy-doctor/truth/zipped/cpu_instrs/${i}.zip" \
          -d gameboy-doctor/truth/unzipped/cpu_instrs/
done
```

2. **Create logs directory**:
```bash
mkdir -p logs
```

### Run All Doctor Tests

```bash
./run_all_doctor_tests.sh
```

### Run Specific Tests

```bash
./run_all_doctor_tests.sh 6           # Run test 6 only
./run_all_doctor_tests.sh 1 3 6       # Run tests 1, 3, and 6
```

### Run Single Test Manually

**Step 1: Generate trace log**
```bash
./obj_dir/test_doctor_compare \
    "test_roms/cpu_instrs/individual/06-ld r,r.gb" \
    "logs/test_6.log" \
    "" \
    50000
```

Arguments:
- `arg1`: ROM file path
- `arg2`: Output log file
- `arg3`: Reference log (optional, for display)
- `arg4`: Number of instructions to log

**Step 2: Compare with gameboy-doctor**
```bash
python3 gameboy-doctor/gameboy-doctor logs/test_6.log cpu_instrs 6
```

### Understanding Doctor Output

**Success:**
```
All 50000 instructions match!
```

**Failure:**
```
Mismatch at line 1234:
  Expected: A:01 F:B0 B:00 C:13 D:00 E:D8 H:01 L:4D SP:FFFE PC:0150
  Got:      A:01 F:80 B:00 C:13 D:00 E:D8 H:01 L:4D SP:FFFE PC:0150
                  ^^
```

The trace format is:
```
A:XX F:XX B:XX C:XX D:XX E:XX H:XX L:XX SP:XXXX PC:XXXX PCMEM:XX,XX,XX,XX
```

- `A`, `B`, `C`, `D`, `E`, `H`, `L`: 8-bit registers
- `F`: Flags register (Z=0x80, N=0x40, H=0x20, C=0x10)
- `SP`: Stack pointer
- `PC`: Program counter
- `PCMEM`: 4 bytes at PC (current instruction)

---

## Rebuilding Test Binaries

### Rebuild test_blargg_serial

```bash
cd /mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator

# Compile
g++ -Os -I. -Iobj_dir \
    -I/usr/local/share/verilator/include \
    -I/usr/local/share/verilator/include/vltstd \
    -DVM_TRACE=1 \
    -c -o obj_dir/test_blargg_serial.o test_blargg_serial.cpp

# Link
cd obj_dir
g++ test_blargg_serial.o \
    /usr/local/share/verilator/include/verilated.cpp \
    /usr/local/share/verilator/include/verilated_vcd_c.cpp \
    /usr/local/share/verilator/include/verilated_threads.cpp \
    Vtop__ALL.a \
    -I. -I/usr/local/share/verilator/include \
    -pthread -lpthread -latomic \
    -o ../test_blargg_serial
```

### Rebuild test_doctor_compare

```bash
cd /mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator

# Compile
g++ -Os -I. -Iobj_dir \
    -I/usr/local/share/verilator/include \
    -I/usr/local/share/verilator/include/vltstd \
    -DVM_TRACE=1 \
    -c -o obj_dir/test_doctor_compare.o test_doctor_compare.cpp

# Link
cd obj_dir
g++ test_doctor_compare.o \
    /usr/local/share/verilator/include/verilated.cpp \
    /usr/local/share/verilator/include/verilated_vcd_c.cpp \
    /usr/local/share/verilator/include/verilated_threads.cpp \
    Vtop__ALL.a \
    -I. -I/usr/local/share/verilator/include \
    -pthread -lpthread -latomic \
    -o test_doctor_compare
```

### Rebuild Verilator Model (after RTL changes)

```bash
cd /mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator
./verilate_gameboy.sh
```

This regenerates `obj_dir/Vtop__ALL.a` from the Verilog sources.

---

## Debug Test Binaries

Additional test binaries for debugging specific issues:

| Binary | Purpose |
|--------|---------|
| `test_int_handler` | Trace interrupt handler execution |
| `test_int_vector` | Debug interrupt vector fetch timing |
| `test_all_iff1` | Track all IFF1 (interrupt enable) changes |
| `test_ei_sequence` | Trace EI instruction behavior |

### Build Debug Test

```bash
cd /mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator

# Compile (replace test_name with actual test)
g++ -Os -I. -Iobj_dir \
    -I/usr/local/share/verilator/include \
    -I/usr/local/share/verilator/include/vltstd \
    -DVM_TRACE=1 \
    -c -o obj_dir/test_int_handler.o test_int_handler.cpp

# Link
cd obj_dir
g++ test_int_handler.o \
    /usr/local/share/verilator/include/verilated.cpp \
    /usr/local/share/verilator/include/verilated_vcd_c.cpp \
    /usr/local/share/verilator/include/verilated_threads.cpp \
    Vtop__ALL.a \
    -I. -I/usr/local/share/verilator/include \
    -pthread -lpthread -latomic \
    -o ../test_int_handler
```

---

## Quick Reference Commands

```bash
# Navigate to test directory
cd /mnt/c/Users/waldo/Documents/GitHub/MyPC/GameBoySimulator/verilator

# Run quick test (06-ld r,r is fastest)
./test_blargg_serial test_roms/cpu_instrs/individual/06-ld\ r,r.gb

# Run with timeout
timeout 3600 ./test_blargg_serial test_roms/cpu_instrs/individual/01-special.gb

# Run all doctor tests
./run_all_doctor_tests.sh

# Run specific doctor test
./run_all_doctor_tests.sh 6

# Manual doctor comparison
./obj_dir/test_doctor_compare "test_roms/cpu_instrs/individual/06-ld r,r.gb" logs/test_6.log "" 50000
python3 gameboy-doctor/gameboy-doctor logs/test_6.log cpu_instrs 6
```

---

## Troubleshooting

### "Test status unclear" - Test hit cycle limit

Increase `max_cycles` in `test_blargg_serial.cpp` and rebuild:
```cpp
int max_cycles = 2000000000;  // 2B cycles
```

### "Cannot open ROM" error

Check ROM path - spaces need escaping:
```bash
./test_blargg_serial "test_roms/cpu_instrs/individual/03-op sp,hl.gb"
# or
./test_blargg_serial test_roms/cpu_instrs/individual/03-op\ sp,hl.gb
```

### "obj_dir/test_doctor_compare not found"

Build the test binary (see Rebuilding section above).

### Reference logs not found

Unzip them:
```bash
for i in 1 2 3 4 5 6 7 8 9 10 11; do
    unzip -o "gameboy-doctor/truth/zipped/cpu_instrs/${i}.zip" \
          -d gameboy-doctor/truth/unzipped/cpu_instrs/
done
```

### Test binary crashes or behaves unexpectedly

Rebuild the Verilator model:
```bash
./verilate_gameboy.sh
```

Then rebuild the test binary.

---

## Test Status (as of last update)

| Test | Blargg Serial | Doctor |
|------|---------------|--------|
| 01-special | ⏳ Running | - |
| 02-interrupts | ⏳ Running (no EI errors) | - |
| 03-op sp,hl | ⏳ Running | - |
| 04-op r,imm | ⏳ Running | - |
| 05-op rp | ⏳ Running | - |
| 06-ld r,r | ✅ PASSED | - |
| 07-jr,jp,call,ret,rst | ⏳ Running | - |
| 08-misc instrs | ⏳ Running | - |
| 09-op r,r | ⏳ Running | - |
| 10-bit ops | ⏳ Running | - |
| 11-op a,(hl) | ⏳ Running | - |

Legend: ✅ Passed, ❌ Failed, ⏳ Running/Untested
