# PCMEM and PC Issues - Root Cause Analysis and Solutions

## Problems Identified

### Issue 1: PCMEM Shows All Zeros
**Symptom:** Logger outputs `PCMEM:00,00,00,00` for all logged instructions

**Root Cause:** Boot ROM memory architecture mismatch
- Boot ROM is uploaded to **internal boot ROM memory** (not SDRAM)
- When `boot_rom_enabled=1`, CPU reads addresses 0x0000-0x00FF from internal boot ROM
- The logger's `read_pcmem()` function reads from **SDRAM model**
- SDRAM model has no access to internal boot ROM memory
- Result: Logger reads zeros from SDRAM instead of actual boot ROM instructions

**Evidence:**
```
# From test_doctor_debug3.cpp output:
Memory dump 0x0000-0x000F (SDRAM):
0000: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00

# Boot ROM was uploaded as C3 50 01 (JP 0x0150) but SDRAM doesn't have it
```

### Issue 2: PC Never Reaches 0x0150
**Symptom:** Test execution stays in PC=0x0165-0x01C8 range, never reaches expected 0x0150

**Root Cause:** CPU executes during boot ROM upload
- Boot ROM upload uses `run_cycles_with_sdram()` between write operations
- CPU is NOT in reset during upload, so it executes
- JP 0x0150 instruction executes during upload process
- CPU jumps to 0x0150 but cart ROM not loaded yet
- CPU executes NOPs from unmapped cart ROM (all zeros)
- By the time test program is loaded at 0x0150, PC is already past it

**Evidence:**
```
# From test_doctor_debug4.cpp output:
After reset, before any boot ROM upload:
  PC = 0x0000

After boot ROM upload, before running:
  PC = 0x015D    ← PC advanced during upload!

# PC jumped from 0x0000 to 0x015D during the upload process
# This means JP 0x0150 executed, then ~13 NOPs ran
```

## Detailed Memory Architecture

### GameBoy Memory Map
```
0x0000-0x00FF: Boot ROM (when boot_rom_enabled=1) OR Cart ROM Bank 0 (when disabled)
0x0100-0x7FFF: Cart ROM
0x8000-0x9FFF: VRAM
0xA000-0xBFFF: Cart RAM
0xC000-0xDFFF: Work RAM
0xFE00-0xFE9F: OAM
0xFF00-0xFF7F: I/O Registers
0xFF80-0xFFFE: High RAM (HRAM)
```

### Boot ROM vs SDRAM
- **Boot ROM upload (`boot_download` interface):**
  - Writes to internal boot ROM memory inside GameBoy core
  - 256 bytes, addresses 0x00-0xFF
  - CPU reads from this when `boot_rom_enabled=1`

- **SDRAM (MisterSDRAMModel):**
  - Stores cart ROM data
  - When boot ROM disabled, addresses 0x00-0xFF also come from SDRAM
  - SDRAM model has no visibility into internal boot ROM

- **Memory Read Priority:**
  ```
  If (address < 0x0100 AND boot_rom_enabled):
      Read from internal boot ROM
  Else:
      Read from SDRAM (cart ROM)
  ```

## Solutions

### Solution 1: Hold CPU in Reset During ROM Upload

**The Correct Method (from test_gui_raster_sanity.cpp):**

```cpp
// Step 1: Hold CPU in reset
dut->reset = 1;
run_cycles_with_sdram(dut, sdram, 200);

// Step 2: Upload boot ROM (CPU won't execute)
download_boot_rom(dut, sdram, boot.data(), boot.size());

// Step 3: Load cart ROM to SDRAM
for (int i = 0; i < test_program_size; i++) {
    sdram->write8(0x0150 + i, test_program[i]);
}

// Step 4: Initialize cart
init_cart_without_writes(dut, sdram);
wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 5000, sdram);

// Step 5: Release reset (CPU starts at PC=0x0000)
run_cycles_with_sdram(dut, sdram, 500);
dut->reset = 0;

// Now CPU executes from 0x0000 with all ROMs loaded!
```

**Why this works:**
- CPU held in reset → PC stays at 0x0000
- Boot ROM uploaded while CPU can't execute
- Cart ROM loaded while CPU can't execute
- When reset released, CPU starts from 0x0000 with complete ROMs

**Comment from test_gui_raster_sanity.cpp:**
```cpp
// Hold the core in reset while we inject the boot ROM and initialize cart state.
// If reset is released too early, the CPU can start executing with an empty boot ROM
// and before cart_ready is asserted, leading to permanent 0x00 reads from ROM.
```

### Solution 2: Add Boot ROM Memory to Logger

For PCMEM to show correct boot ROM bytes, the logger needs access to boot ROM data.

**Modify gb_doctor_logger.h:**

```cpp
class GBDoctorLogger {
private:
    uint8_t boot_rom[256];  // Copy of boot ROM
    bool boot_rom_available;

public:
    // Add method to store boot ROM copy
    void set_boot_rom(const uint8_t* rom, size_t size) {
        if (size > 256) size = 256;
        memcpy(boot_rom, rom, size);
        if (size < 256) memset(boot_rom + size, 0, 256 - size);
        boot_rom_available = true;
    }

    // Updated read_pcmem implementation
    template<typename DUT>
    void read_pcmem(DUT* dut, MisterSDRAMModel* sdram, uint16_t pc, uint8_t* out) {
        for (int i = 0; i < 4; i++) {
            uint16_t addr = (pc + i) & 0xFFFF;

            // Check if address is in boot ROM range and boot ROM is enabled
            if (addr < 0x0100 && dut->dbg_boot_rom_enabled && boot_rom_available) {
                // Read from boot ROM copy
                out[i] = boot_rom[addr];
            } else if (addr < 0x8000) {
                // Cart ROM area - read from SDRAM
                out[i] = sdram->read_byte(addr);
            } else if (addr >= 0x8000 && addr < 0xA000) {
                // VRAM
                out[i] = sdram->read_byte(addr);
            } else if (addr >= 0xC000 && addr < 0xE000) {
                // Work RAM
                out[i] = sdram->read_byte(addr);
            } else {
                // I/O, OAM, HRAM - not in SDRAM
                out[i] = 0x00;
            }
        }
    }
};
```

**Usage:**
```cpp
// After loading boot ROM
GBDoctorLogger logger("logs/output.log");
logger.set_boot_rom(boot_rom_data, 256);

// Now PCMEM will correctly show boot ROM bytes
```

### Solution 3: Only Log After Boot ROM Completes (Recommended)

**Simplest approach for most testing:**

```cpp
// In main test loop
if (dut->dbg_boot_rom_enabled == 0) {
    // Boot ROM has completed, now log cart ROM execution
    logger.tick(dut, sdram);
}
```

**Advantages:**
- No need to copy boot ROM to logger
- Simpler implementation
- Focuses on cart ROM (the code we're testing)
- PCMEM reads work correctly (all from SDRAM after boot)

**Disadvantages:**
- Can't log boot ROM execution
- Won't catch bugs in boot ROM sequence

**When to use:**
- Testing cart ROM code (most common case)
- Using doctor boot ROM that just initializes and jumps
- Debugging game code, not boot ROM

## Corrected Test Template

**File: test_doctor_corrected.cpp**

```cpp
#include <verilated.h>
#include "Vtop.h"
#include "gb_test_common.h"
#include "gb_doctor_logger.h"

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);

    Vtop* dut = new Vtop();
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8, INTERFACE_NATIVE_SDRAM);
    sdram->cas_latency = 2;

    // Initialize
    reset_dut_with_sdram(dut, sdram);

    // STEP 1: Hold CPU in reset
    printf("Holding CPU in reset...\n");
    dut->reset = 1;
    run_cycles_with_sdram(dut, sdram, 200);

    // STEP 2: Load boot ROM
    printf("Loading boot ROM...\n");
    uint8_t boot_rom[256];
    memset(boot_rom, 0x00, sizeof(boot_rom));
    boot_rom[0x000] = 0xC3;  // JP 0x0150
    boot_rom[0x001] = 0x50;
    boot_rom[0x002] = 0x01;

    dut->boot_download = 1;
    dut->boot_wr = 0;
    for (int addr = 0; addr < 256; addr += 2) {
        uint16_t w = boot_rom[addr] | ((uint16_t)boot_rom[addr + 1] << 8);
        dut->boot_addr = addr;
        dut->boot_data = w;
        dut->boot_wr = 1;
        run_cycles_with_sdram(dut, sdram, 4);
        dut->boot_wr = 0;
        run_cycles_with_sdram(dut, sdram, 4);
    }
    dut->boot_download = 0;

    // STEP 3: Load test program to SDRAM
    printf("Loading test program to SDRAM...\n");
    uint8_t test_program[] = {
        0x00,               // 0150: NOP
        0x3E, 0x42,        // 0151: LD A, $42
        0x47,               // 0153: LD B, A
        0x04,               // 0154: INC B
        0x18, 0xFE,        // 0155: JR -2 (loop)
    };
    for (int i = 0; i < sizeof(test_program); i++) {
        sdram->write8(0x0150 + i, test_program[i]);
    }

    // Cart header
    sdram->write8(0x0100, 0x00);  // NOP
    sdram->write8(0x0101, 0xC3);  // JP 0x0150
    sdram->write8(0x0102, 0x50);
    sdram->write8(0x0103, 0x01);

    // Nintendo logo (required for boot ROM)
    const uint8_t logo[48] = {
        0xCE, 0xED, 0x66, 0x66, 0xCC, 0x0D, 0x00, 0x0B,
        0x03, 0x73, 0x00, 0x83, 0x00, 0x0C, 0x00, 0x0D,
        0x00, 0x08, 0x11, 0x1F, 0x88, 0x89, 0x00, 0x0E,
        0xDC, 0xCC, 0x6E, 0xE6, 0xDD, 0xDD, 0xD9, 0x99,
        0xBB, 0xBB, 0x67, 0x63, 0x6E, 0x0E, 0xEC, 0xCC,
        0xDD, 0xDC, 0x99, 0x9F, 0xBB, 0xB9, 0x33, 0x3E,
    };
    for (int i = 0; i < 48; i++) {
        sdram->write8(0x0104 + i, logo[i]);
    }

    // STEP 4: Initialize cart
    printf("Initializing cart...\n");
    dut->ioctl_download = 1;
    dut->ioctl_index = 0;
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_download = 0;
    run_cycles_with_sdram(dut, sdram, 64);
    dut->ioctl_addr = 0;
    dut->ioctl_dout = 0;
    dut->ioctl_wr = 1;
    run_cycles_with_sdram(dut, sdram, 4);
    dut->ioctl_wr = 0;
    run_cycles_with_sdram(dut, sdram, 256);

    wait_for_condition(dut, [&]() { return dut->dbg_cart_ready; }, 10000, sdram);

    // STEP 5: Release reset
    printf("Releasing reset...\n");
    run_cycles_with_sdram(dut, sdram, 500);
    dut->reset = 0;

    printf("PC after reset release: 0x%04X (should be 0x0000)\n", dut->dbg_cpu_pc);

    // STEP 6: Create logger
    GBDoctorLogger logger("logs/corrected_output.log", true);
    logger.set_boot_rom(boot_rom, 256);  // Optional: for boot ROM PCMEM
    logger.set_enabled(true);

    // STEP 7: Run and log
    printf("Running simulation...\n");
    uint16_t prev_pc = 0;
    int instruction_count = 0;

    for (int cycle = 0; cycle < 50000 && instruction_count < 200; cycle++) {
        tick_with_sdram(dut, sdram);
        logger.tick(dut, sdram);

        uint16_t curr_pc = dut->dbg_cpu_pc;
        if (curr_pc != prev_pc) {
            instruction_count++;

            // Stop if we reach infinite loop
            if (curr_pc == 0x0155) {  // JR -2 at 0x0155
                printf("Reached infinite loop at 0x0155 after %d instructions\n",
                    instruction_count);
                break;
            }
        }
        prev_pc = curr_pc;
    }

    printf("Test complete. Logged %lu instructions.\n",
        (unsigned long)logger.get_instruction_count());

    delete dut;
    delete sdram;

    return 0;
}
```

## Summary

### PCMEM Issue
**Problem:** Logger reads SDRAM, but boot ROM is in separate internal memory
**Solution:** Copy boot ROM to logger OR only log after boot ROM disables

### PC Issue
**Problem:** CPU executes during boot ROM upload, runs past intended start
**Solution:** Hold CPU in reset during all ROM uploads

### Key Takeaway
Follow test_gui_raster_sanity.cpp pattern:
1. Reset CPU
2. Load all ROMs
3. Initialize cart
4. Release reset
5. CPU starts from 0x0000 with complete system

## Test Results Expected (After Fix)

With corrected test:
```
Logged 50+ instructions
PC sequence: 0x0000 → 0x0100 → 0x0150 → 0x0151 → 0x0153 → 0x0154 → 0x0155 → loop
PCMEM shows actual instruction bytes (not zeros)
```

## Files Modified

1. **gb_doctor_logger.h** - Add boot ROM support to read_pcmem()
2. **test_doctor_simple.cpp** - Use reset during ROM upload
3. **All future doctor tests** - Follow corrected template

## References

- test_gui_raster_sanity.cpp:103-126 - Correct ROM upload sequence
- MCYCLE_DEBUG_RESULTS.md - M-cycle detection fix
- gb_doctor_logger.h - Logger implementation
