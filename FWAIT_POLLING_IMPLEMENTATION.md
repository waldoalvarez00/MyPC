# FWAIT (WAIT) Instruction - Full Polling Implementation

## Summary

Implemented complete 8087/8086-authentic FPU polling behavior for the FWAIT instruction, including:
- BUSY pin polling with interrupt yield
- ERROR pin detection
- INT 16 exception triggering on FPU errors

## Implementation Status: ✅ Complete and Tested

All 3 test scenarios pass:
1. **FPU Ready**: FWAIT completes immediately when FPU is not busy
2. **FPU Busy**: FWAIT polls BUSY pin in a loop, completes when FPU ready
3. **FPU Error**: FWAIT detects ERROR pin and triggers INT 16 (coprocessor error interrupt)

## Architecture

### Microcode Sequence

```
.at 0x9b;  // FWAIT opcode
    jmp fwait_poll_busy;

fwait_poll_busy:
    // Poll BUSY pin - loop while FPU is busy
    // ext_int_yield allows interrupts during wait
    jmp_if_fpu_busy fwait_poll_busy, ext_int_yield;

fwait_check_error:
    // FPU no longer busy - check ERROR pin
    jmp_if_fpu_error fpu_exception;
    // No error - complete normally
    next_instruction;

fpu_exception:
    // ERROR pin detected - trigger INT 16
    b_sel IMMEDIATE, immediate 0x10, alu_op SELB, tmp_wr_en, jmp do_int;
```

### New Jump Types Added

Added two new conditional jump types to the microcode sequencer:

1. **JumpType_FPU_BUSY** (4'd10)
   - Condition: `fpu_busy` signal (FPU BUSY pin)
   - Usage: `jmp_if_fpu_busy <label>`
   - Semantics: Jump to label if fpu_busy=1, otherwise fall through

2. **JumpType_FPU_ERROR** (4'd11)
   - Condition: `fpu_int` signal (FPU ERROR pin)
   - Usage: `jmp_if_fpu_error <label>`
   - Semantics: Jump to label if fpu_int=1, otherwise fall through

### Signal Flow

```
CPU Core → fpu_int (ERROR pin) → Microcode sequencer
CPU Core → fpu_busy (BUSY pin) → Microcode sequencer

Microcode sequencer → JumpType_FPU_BUSY → jump_target calculation
Microcode sequencer → JumpType_FPU_ERROR → jump_target calculation
```

## Files Modified

### Microcode Infrastructure

1. **utils/microassembler/microcode/Microcode.sv.templ** (lines 223-224)
   - Added FPU jump type handlers to template
   ```systemverilog
   JumpType_FPU_BUSY: jump_target = fpu_busy ? current.next : addr + 1'b1;
   JumpType_FPU_ERROR: jump_target = fpu_int ? current.next : addr + 1'b1;
   ```

2. **utils/microassembler/microcode/wait.us** (lines 18-39)
   - Implemented full FWAIT polling logic with BUSY/ERROR checking
   - Replaced simplified `next_instruction` with polling loop

3. **Quartus/rtl/CPU/InstructionDefinitions.sv** (generated)
   - Regenerated with FPU jump types included in sequencer logic
   - Now includes cases for JumpType_FPU_BUSY and JumpType_FPU_ERROR

### Test Files

4. **modelsim/fpu_wait_polling_tb.sv** (new, 401 lines)
   - Comprehensive test suite for FWAIT polling behavior
   - Tests all 3 scenarios: ready, busy polling, error detection
   - **Result: 3/3 tests passed** ✅

5. **modelsim/fpu_wait_debug_tb.sv** (new, 249 lines)
   - Address trace debugging test
   - Used to diagnose microcode sequencer behavior

## Test Results

### New Test: fpu_wait_polling_tb

```
=== Test 1: FWAIT with FPU ready (not busy, no error) ===
  PASS: FWAIT completed immediately when FPU ready (cycles=5)

=== Test 2: FWAIT with FPU initially busy ===
  FWAIT started, polling FPU BUSY...
  Cleared FPU BUSY after 5 poll cycles
  PASS: FWAIT polled BUSY pin and completed after busy cleared

=== Test 3: FWAIT with ERROR pin asserted ===
  FWAIT started, checking ERROR pin...
  PASS: ERROR detected, INT 16 (0x10) triggered

Test Results:
  PASSED: 3
  FAILED: 0
```

### Existing Test: fpu_wait_minimal

- **Status**: PASS (100% pass rate maintained)
- Confirms backward compatibility with existing FWAIT test infrastructure

## How It Works

### 1. FWAIT Execution Start
- CPU decodes opcode 0x9B
- Microcode sequencer jumps to address 0x9B
- Executes unconditional jump to `fwait_poll_busy` label

### 2. BUSY Pin Polling
- At `fwait_poll_busy`: conditional jump based on `fpu_busy` signal
- If `fpu_busy=1`: jumps back to self (polling loop)
- If `fpu_busy=0`: falls through to `fwait_check_error`
- `ext_int_yield` flag allows interrupts to be serviced during wait

### 3. ERROR Pin Check
- At `fwait_check_error`: conditional jump based on `fpu_int` signal
- If `fpu_int=1`: jumps to `fpu_exception` handler
- If `fpu_int=0`: executes `next_instruction` (normal completion)

### 4. Exception Handling
- At `fpu_exception`: loads immediate value 0x10 (INT 16)
- Stores to temporary register via ALU
- Jumps to `do_int` (common interrupt dispatch microcode)
- This triggers the coprocessor error interrupt vector

## Authentic 8086/8087 Behavior

This implementation matches the real 8086/8087 coprocessor protocol:

1. **Polling, not interrupts**: The 8086 WAIT instruction actively polls the TEST pin (connected to 8087 BUSY), rather than using interrupt-driven synchronization

2. **ERROR pin**: The 8087's ERROR pin (connected to CPU's NMI or dedicated interrupt) signals arithmetic exceptions after an operation completes

3. **INT 16 vector**: The standard PC/XT BIOS assigns interrupt vector 16 (0x10) to coprocessor errors

4. **Interrupt yield**: The `ext_int_yield` flag allows the CPU to service hardware interrupts (IRQ, NMI) while waiting for the FPU, preventing system lockup

## Integration Points

### CPU Core (Core.sv)
- Provides `fpu_busy` and `fpu_int` signals from FPU interface
- These signals are passed through to Microcode module

### FPU (FPU8087_Integrated.v)
- Asserts `cpu_fpu_busy` during ESC instruction execution
- Asserts `cpu_fpu_error` if arithmetic exception occurs
- CPU maps these to `fpu_busy` and `fpu_int` in Core.sv

### Microcode Sequencer (InstructionDefinitions.sv)
- Evaluates conditional jumps based on `fpu_busy` and `fpu_int`
- Controls microcode address flow for polling loops
- Handles interrupt yield during wait states

## Build Instructions

### Rebuild Microcode

```bash
cd utils/microassembler/
python uasm.py outputbin/microcode.bin outputbin/microcode.mif \
    ../../Quartus/rtl/CPU/InstructionDefinitions.sv \
    outputbin/MicrocodeTypes.sv outputbin/MicrocodeTypes.h \
    microcode/*.us
```

### Run Tests

```bash
cd modelsim/
# Run new polling test
iverilog -g2012 -o fpu_wait_polling_tb -I../Quartus/rtl/CPU \
    fpu_wait_polling_tb.sv ../Quartus/rtl/CPU/InstructionDefinitions.sv
./fpu_wait_polling_tb

# Run existing minimal test
python3 test_runner.py --test fpu_wait_minimal
```

### FPGA Synthesis

```bash
cd Quartus/
quartus_sh --flow compile mycore
```

## Performance Considerations

### Cycle Count

- **FPU ready**: ~5 cycles (minimal overhead)
- **FPU busy**: 1 cycle per poll iteration + FPU operation time
- **ERROR handling**: Adds INT 16 dispatch overhead (~50-100 cycles)

### Interrupt Latency

- `ext_int_yield` ensures interrupts can be serviced during long FPU operations
- Typical FPU operations (FADD, FMUL): 10-40 cycles
- Transcendental operations (FSIN, FATAN): 100-200 cycles
- Without yield, interrupts would be blocked during entire FWAIT

## Next Steps

### Suggested Enhancements

1. **Add test to Python test suite**: Register fpu_wait_polling_tb in test_configs.py
2. **Integration testing**: Test FWAIT in combination with actual FPU ESC instructions
3. **Hardware validation**: Test on real MiSTer FPGA with FPU-using software
4. **BIOS INT 16 handler**: Implement INT 16 handler in BIOS (utils/bios/) to display/log FPU errors

### Production Readiness

- ✅ Microcode implementation complete
- ✅ Jump type infrastructure added
- ✅ Unit tests pass (3/3)
- ✅ Backward compatibility maintained
- ✅ Authentic 8086/8087 behavior
- ⏳ FPGA synthesis pending (requires full rebuild)
- ⏳ Integration testing with real FPU operations

## References

- Intel 8086 Family User's Manual (Section 2.5: Processor Extension Interface)
- Intel 8087 Math Coprocessor Datasheet (BUSY and ERROR pin specifications)
- PC/XT Technical Reference (INT 16 coprocessor error handler)
- s80x86 project: Original CPU microcode architecture (wait.us)

---

**Implementation Date**: November 30, 2025
**Status**: Complete and tested
**Test Results**: 3/3 passed (100%)
