# FPU Exception Handling Architecture Index

This directory contains comprehensive documentation for the FPU8087 exception handling system.

## Quick Start Documents

### 1. **FPU8087_IE_Quick_Reference.md** ← START HERE
Quick lookup tables and checklists for Invalid Operation (IE) exception testing.
- Status word/control word bit layouts
- IE trigger conditions
- Signal flows
- Key instructions & constants
- File references

### 2. **FPU8087_Exception_Handling_Analysis.md** ← DETAILED REFERENCE
Complete architectural analysis with code references and implementation details.

**Sections:**
- **Section 1**: Status Word bit layout (16-bit register structure)
- **Section 2**: Key signals for exception reporting (data flows)
- **Section 3**: Stack management mechanism (TOP pointer, tag word, overflow/underflow)
- **Section 4**: Invalid Operation (IE) exception types and triggers
- **Section 5**: Existing FPU testbench patterns and structures
- **Section 6**: Recommended test cases for IE testbenches
- **Section 7**: Control flow and timing for IE exception handling
- **Section 8**: Implementation notes and critical signals to monitor

## Key Findings

### Status Word Structure
- **Bit 0**: IE (Invalid Operation) flag ← TARGET FOR IE TESTBENCHES
- **Bit 6**: SF (Stack Fault) - combines overflow and underflow
- **Bit 7**: ES (Exception Summary) - auto-set if ANY exception occurs
- **Bits 13:11**: TOP (Stack Pointer) - selects logical ST(0)

### Exception Signal Path for IE
1. Arithmetic Unit detects invalid condition → `arith_invalid = 1`
2. Exception Handler latches exception → `exception_invalid_latched <= 1`
3. INT assertion check → `if (exception_invalid && !mask_invalid) int_request <= 1`
4. Status Word updates → `status_word[0] = 1`, `status_word[7] = 1`

### Stack Management
- **Tag Word**: 2 bits per register (00=valid, 01=zero, 10=special, 11=empty)
- **Stack Pointer (TOP)**: Bits 13:11 of status word, range 0-7
- **Mapping**: Physical = (TOP + logical_index) & 0x7

### IE Exception Triggers
1. SNaN operand in any operation
2. **Stack empty** - Operating on ST(i) when tag=11
3. Inf+(-Inf) operations
4. 0×Inf multiplications
5. 0/0 or Inf/Inf divisions
6. sqrt(negative)

## File Organization

### Core Exception Modules
- `FPU_Exception_Handler.v` - Exception latching and INT signal generation
- `FPU_StatusWord.v` - Status word construction (all exception flags)
- `FPU_RegisterStack.v` - Stack management with tag word
- `FPU_ControlWord.v` - Control word parsing and mask bit extraction

### Integration
- `FPU_Core.v` - Top-level FPU module integrating all subsystems
- `FPU_ArithmeticUnit.v` - Detects actual exception conditions

### Testbenches
- `modelsim/fpu_core_tb.sv` - Primary reference testbench (466 lines)
- `modelsim/run_fpu_core_test.sh` - Execution script with iverilog compilation
- `modelsim/fpu_format_converter_tb.sv` - Alternative example patterns

## Testing Pattern Template

For IE exception testbenches, follow this pattern:

```systemverilog
// 1. Clock and reset setup
initial begin
    clk = 0;
    forever #10 clk = ~clk;  // 50 MHz
end

// 2. Initialize FPU
reset = 1;
repeat(20) @(posedge clk);
reset = 0;

// 3. Set control word (unmask IE to see int_request)
control_in = 16'h027F;  // IE unmasked (bit 0 = 0)
control_write = 1;
@(posedge clk);
control_write = 0;

// 4. Execute test instruction
instruction = INST_FADD;
execute = 1;
@(posedge clk);
execute = 0;

// 5. Wait for completion
repeat(500) @(posedge clk) if (ready) break;

// 6. Check results
assert(status_out[0] == 1) else $error("IE flag not set");
assert(int_request == 1) else $error("int_request not asserted");
```

## Default Values

| Item | Value | Meaning |
|------|-------|---------|
| Default Control Word | 0x037F | All exceptions masked |
| IE Unmasked Control | 0x027F | IE exception enabled |
| FP80 One | 0x3FFF_8000000000000000 | 1.0 in extended precision |
| Stack Empty Tag | 0b11 | Register uninitialized |
| Stack Valid Tag | 0b00 | Register contains valid data |

## Exception Flags in Status Word

| Bit | Name | Code | Description |
|-----|------|------|-------------|
| 0 | IE | Invalid Operation | SNaN, stack empty, invalid arithmetic |
| 1 | DE | Denormalized Operand | Operand is subnormal |
| 2 | ZE | Zero Divide | Division by zero |
| 3 | OE | Overflow | Result > max representable |
| 4 | UE | Underflow | Result < min representable |
| 5 | PE | Precision | Inexact result (rounded) |
| 6 | SF | Stack Fault | Overflow or underflow on stack |
| 7 | ES | Exception Summary | Any flag 0-6 set |

## Implementation Checklist for IE Testbenches

- [ ] Define FP80 test constants (zero, one, NaN, Inf, etc.)
- [ ] Create helper tasks: `wait_for_ready()`, `execute_instruction()`, `test_instruction()`
- [ ] Initialize FPU with FINIT instruction
- [ ] Set control word to unmask IE (0x027F)
- [ ] Test SNaN operand handling
- [ ] Test stack empty detection
- [ ] Test invalid arithmetic patterns
- [ ] Verify status_out[0] (IE flag) assertion
- [ ] Verify int_request signal timing
- [ ] Test FCLEX clearing exceptions
- [ ] Verify exception is sticky until cleared
- [ ] Test masked IE (no int_request)
- [ ] Report pass/fail counts

## Related Documentation

- `docs/HARVARD_CACHE_ARCHITECTURE.md` - Cache design (context for memory operations)
- `docs/TESTING_SUMMARY.md` - Overall test status (165/165 FPU tests passing)
- `docs/FPU_*.md` - Other FPU-specific documentation files
- `CLAUDE.md` - Project build and architecture overview

## Contact & References

- FPU Implementation: Waldo Alvarez, https://pipflow.com
- License: GPL 2.0
- Platform: MiSTer DE10-Nano (Intel Cyclone V FPGA)
- Test Framework: Icarus Verilog
- Current Status: 165/165 FPU tests passing (100%)

