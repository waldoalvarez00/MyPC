# FPU8087 Exception Handling Architecture Analysis

## 1. STATUS WORD BIT LAYOUT

### Structure (16-bit register):
```
[15]    : Busy (B) flag
[14]    : Condition Code C3
[13:11] : Stack Top Pointer (TOP) - selects logical ST(0)
[10]    : Condition Code C2
[9]     : Condition Code C1 (used for stack faults)
[8]     : Condition Code C0
[7]     : Exception Summary (ES) - set if ANY arithmetic exception
[6]     : Stack Fault (SF) - stack overflow OR underflow occurred
[5]     : Precision Exception (PE) - inexact result
[4]     : Underflow Exception (UE)
[3]     : Overflow Exception (OE)
[2]     : Zero Divide Exception (ZE)
[1]     : Denormalized Operand Exception (DE)
[0]     : Invalid Operation Exception (IE) ← TARGET FOR IE TESTBENCHES
```

### Key Properties:
- **Exception Summary (ES, bit 7)** is automatically set if ANY exception flag (bits 0-5) is set
- **Stack Fault (SF, bit 6)** combines both stack overflow and underflow detection
- **Condition Code C1 (bit 9)** has dual purpose:
  - Normally: comparison result bit
  - Stack fault context: indicates overflow (1) or underflow (0)
- **Stack Pointer (bits 13:11)** is the TOP value - points to current ST(0) position
- **All exception flags are STICKY** - once set, remain until explicitly cleared
- **Note**: IE is bit 0 in status word (confirmed by FPU_StatusWord.v lines 150 and 23)

### File References:
- `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_StatusWord.v` - Primary implementation
- `/home/user/MyPC2/Quartus/rtl/FPU8087/8087Status.v` - Alternative declaration module

---

## 2. KEY SIGNALS FOR EXCEPTION REPORTING

### From FPU_Core.v:

#### Exception Inputs (from Arithmetic Unit):
```
wire arith_invalid      ← Invalid operation detected
wire arith_denormal     ← Denormal operand detected
wire arith_zero_div     ← Division by zero detected
wire arith_overflow     ← Result overflow detected
wire arith_underflow    ← Result underflow detected
wire arith_inexact      ← Precision loss (maps to precision exception)
```

#### Exception Control from Control Word:
```
wire mask_invalid       ← 1 = exception masked (disabled), 0 = exception enabled
wire mask_denormal      ← Same masking logic for denormal operands
wire mask_zero_div      ← Same masking logic for zero divide
wire mask_overflow      ← Same masking logic for overflow
wire mask_underflow     ← Same masking logic for underflow
wire mask_precision     ← Same masking logic for precision (inexact)
```

#### Stack Fault Signals:
```
wire stack_overflow     ← Detected when pushing into non-empty register
wire stack_underflow    ← Detected when popping from empty register
→ Combined into: status_stack_fault = stack_overflow | stack_underflow
```

#### Top-Level Output:
```
output int_request      ← Active HIGH (8087-style)
                           Asserted when unmasked exception occurs
                           Remains asserted until FCLEX/FNCLEX executed
```

### Signal Path for IE (Invalid Operation):
1. **Arithmetic Unit detects invalid condition** → `arith_invalid` = 1
2. **Exception Handler latches exception** (line 153 in FPU_Exception_Handler.v):
   ```
   exception_invalid_latched <= exception_invalid_latched || exception_invalid;
   ```
3. **INT assertion** (line 163-170 in FPU_Exception_Handler.v):
   ```
   if ((exception_invalid && !mask_invalid) || ...) begin
       int_request <= 1'b1;
       exception_pending <= 1'b1;
   end
   ```
4. **Status Word Update** (line 120 in FPU_StatusWord.v):
   ```
   if (invalid) exc_invalid <= 1'b1;
   ```
5. **ES (Exception Summary) Auto-Set** (line 73 in FPU_StatusWord.v):
   ```
   wire exception_summary;
   assign exception_summary = exc_invalid | exc_denormal | exc_zero_div | ...
   ```

### Files:
- `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_Exception_Handler.v` - Exception latching
- `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_Core.v` - Signal integration
- `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_ControlWord.v` - Mask bit decoding

---

## 3. STACK MANAGEMENT MECHANISM

### Stack Pointer (TOP):
- **Location**: Status word bits [13:11]
- **Range**: 0-7 (3-bit pointer)
- **Direction**: Decrements on push, increments on pop
- **Physical-to-Logical Mapping Function** (in FPU_RegisterStack.v, lines 97-102):
  ```
  Physical Register = (stack_ptr + logical_index) & 3'b111
  
  Example: If TOP = 3 (points to physical register 3 as ST(0)):
    - ST(0) logical → Physical register 3
    - ST(1) logical → Physical register 4
    - ST(7) logical → Physical register 2
  ```

### Tag Word Structure (16-bit):
```
Format: 2 bits per register × 8 registers = 16 bits
[1:0]   = Tag for ST(0) (top of stack, after TOP rotation)
[3:2]   = Tag for ST(1)
[5:4]   = Tag for ST(2)
[7:6]   = Tag for ST(3)
[9:8]   = Tag for ST(4)
[11:10] = Tag for ST(5)
[13:12] = Tag for ST(6)
[15:14] = Tag for ST(7)

Tag Values:
  00 = Valid (non-zero)
  01 = Zero
  10 = Special (NaN, Infinity, Denormal)
  11 = Empty ← KEY FOR INVALID OPERATION DETECTION
```

### Stack Overflow/Underflow Detection:

#### Overflow (pushing into non-empty slot):
```
Detected in FPU_RegisterStack.v, lines 140-144:
  if (push) begin
      new_stack_ptr = stack_ptr - 3'd1;
      if (tags[(new_stack_ptr + 3'd7) & 3'b111] != 2'b11) begin
          stack_overflow <= 1'b1;  ← Non-empty slot detected
      end
  end
```

#### Underflow (popping from empty slot):
```
Detected in FPU_RegisterStack.v, lines 146-149:
  if (pop) begin
      if (tags[physical_reg(3'd0)] == 2'b11) begin  ← Empty detected
          stack_underflow <= 1'b1;
      end
  end
```

#### Both Errors Combined:
```
In FPU_Core.v (around line 380):
status_stack_fault <= stack_overflow | stack_underflow;
→ Sets SF (Stack Fault) in status word, bit 6
→ Also sets C1 (Condition Code 1) as indicator
```

### Tag Word Automatic Generation:
Function in FPU_RegisterStack.v, lines 69-91:
```
function generate_tag(value):
  if (exponent == 0 && mantissa == 0):
    return 01  ← Zero
  else if (exponent == 0x7FFF):
    return 10  ← Infinity or NaN
  else if (exponent == 0 && mantissa != 0):
    return 10  ← Denormal
  else:
    return 00  ← Valid
```

### Critical Operations:
1. **FINIT** (Initialize): Sets all tags to 11 (empty), TOP=0
2. **FFREE** (Free Register): Marks specific register as 11 (empty)
3. **FINCSTP** (Increment): TOP++
4. **FDECSTP** (Decrement): TOP--
5. **Push/Pop**: Automatically check tag on top register

### Files:
- `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_RegisterStack.v` - Stack implementation
- `/home/user/MyPC2/Quartus/rtl/FPU8087/tagRegister.v` - Tag register storage
- `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_StatusWord.v` - Status word assembly

---

## 4. INVALID OPERATION (IE) EXCEPTION TYPES

### Conditions that trigger IE (arith_invalid = 1):

1. **SNaN (Signaling NaN) Operand** (most common IE cause)
   - Any arithmetic operation on SNaN triggers IE
   - Result is QNaN (Quiet NaN) if masked

2. **Stack Empty Operation** (CRITICAL FOR TESTBENCHES)
   - Operating on empty register (tag = 11)
   - Reading from ST(i) when empty
   - Example: Division when ST(0) or ST(1) empty

3. **Invalid Arithmetic Patterns**:
   - **Addition**: Inf + (-Inf) or Inf - Inf (same sign)
   - **Multiplication**: 0 × Inf or Inf × 0
   - **Division**: 0/0 or Inf/Inf
   - **Square Root**: sqrt(negative) where operand is real negative

4. **Conversion Invalid Cases**:
   - Converting NaN to integer → returns 0x8000_0000 (INT32) or 0x8000 (INT16)
   - Converting overflow values → returns saturated integer

### Detection Code in FPU_Core.v:

Around lines 200-300 (ArithmeticUnit connections), invalid flag flows from:
```
FPU_ArithmeticUnit.flag_invalid 
  → exception_handler.exception_invalid 
    → status_word.exc_invalid (bit 0)
    → status_word.exception_summary (bit 7)
```

---

## 5. EXISTING FPU TESTBENCH PATTERNS

### Overall Structure (from fpu_core_tb.sv):

```systemverilog
// 1. CLOCK AND RESET
initial begin
    clk = 0;
    forever #10 clk = ~clk;  // 50 MHz clock
end

// 2. SIGNAL DECLARATIONS
reg clk;
reg reset;
reg [7:0] instruction;
reg [2:0] stack_index;
reg execute;
wire ready;
wire error;
...
integer test_count, pass_count, fail_count, timeout_count;

// 3. DUT INSTANTIATION
FPU_Core dut (
    .clk(clk),
    .reset(reset),
    .instruction(instruction),
    ...
    .int_request(int_request)
);

// 4. HELPER TASKS
task wait_for_ready;
    input integer max_cycles;
    ... wait for ready signal with timeout
endtask

task execute_instruction;
    input [7:0] inst;
    input [2:0] st_idx;
    input [79:0] data;
    ... pulse execute, wait for ready
endtask

task test_instruction;
    input [7:0] inst;
    input [255:0] test_name;
    ... execute, check results, track pass/fail
endtask

// 5. TEST GROUPS (organized by category)
initial begin
    reset = 1;
    repeat(20) @(posedge clk);
    reset = 0;
    
    // Group 1: Initialization
    test_instruction(INST_FINIT, ...);
    
    // Group 2: Stack Operations
    test_instruction(INST_FLD, ...);
    test_instruction(INST_FST, ...);
    
    // ... more groups ...
    
    // Group 6: Exception Handling
    test_instruction(INST_FCLEX, ...);  // Clear exceptions
    test_instruction(INST_FLD, ...);
    test_instruction(INST_FDIV, ...);   // Test zero divide
    
    // 6. SUMMARY REPORTING
    $display("Total tests: %0d", test_count);
    $display("Passed: %0d", pass_count);
    ...
    $finish;
end
```

### Key Instruction Opcodes (from testbench):
```
// Arithmetic
INST_FADD  = 8'h10;   // ST(0) = ST(0) + ST(i)
INST_FSUB  = 8'h12;   // ST(0) = ST(0) - ST(i)
INST_FMUL  = 8'h14;   // ST(0) = ST(0) * ST(i)
INST_FDIV  = 8'h16;   // ST(0) = ST(0) / ST(i)

// Stack
INST_FLD   = 8'h20;   // Push onto stack
INST_FST   = 8'h21;   // Store (no pop)
INST_FSTP  = 8'h22;   // Store and pop
INST_FXCH  = 8'h23;   // Exchange ST(0) with ST(i)

// Control
INST_FINIT = 8'hF0;   // Initialize FPU
INST_FCLEX = 8'hF4;   // Clear exceptions
INST_FWAIT = 8'hF5;   // Wait for completion

// Integer conversion
INST_FILD32 = 8'h31;  // Load 32-bit integer
INST_FIST32 = 8'h33;  // Store 32-bit integer
```

### FP80 Constant Definition Pattern:
```
localparam FP80_ZERO    = 80'h0000_0000000000000000;
localparam FP80_ONE     = 80'h3FFF_8000000000000000;
localparam FP80_TWO     = 80'h4000_8000000000000000;
localparam FP80_NEG_ONE = 80'hBFFF_8000000000000000;
localparam FP80_PI_4    = 80'h3FFE_C90FDAA22168C235;

// Format: [79:64] = exponent (biased by 16383)
//         [63]    = integer bit (implicit 1)
//         [62:0]  = mantissa
```

### Test Script Pattern (run_fpu_core_test.sh):
```bash
#!/bin/bash
# Compile with iverilog
iverilog -g2012 -o modelsim/fpu_core_tb.vvp \
    -I Quartus/rtl/FPU8087 \
    -DICARUS \
    Quartus/rtl/FPU8087/FPU_Core.v \
    Quartus/rtl/FPU8087/FPU_RegisterStack.v \
    ... (all dependency files) ...
    modelsim/fpu_core_tb.sv

# Run
vvp modelsim/fpu_core_tb.vvp

# Cleanup
rm -f modelsim/fpu_core_tb.vvp
```

### Control Word Setup Pattern:
```
// Default: 0x037F = All exceptions masked, round to nearest, extended precision
localparam DEFAULT_CONTROL = 16'h037F;

// Bit layout:
// [15:12] = Reserved
// [11:10] = Rounding control (00=nearest)
// [9:8]   = Precision (11=extended)
// [7:6]   = Reserved
// [5]     = Mask Precision (1=masked)
// [4]     = Mask Underflow (1=masked)
// [3]     = Mask Overflow (1=masked)
// [2]     = Mask Zero Divide (1=masked)
// [1]     = Mask Denormal (1=masked)
// [0]     = Mask Invalid (1=masked) ← TO ENABLE IE: Use 0x027F
```

### Files:
- `/home/user/MyPC2/modelsim/fpu_core_tb.sv` - Main FPU testbench
- `/home/user/MyPC2/modelsim/run_fpu_core_test.sh` - Test execution script
- `/home/user/MyPC2/modelsim/fpu_format_converter_tb.sv` - Format conversion examples

---

## 6. TESTING INVALID OPERATION (IE) EXCEPTIONS

### Recommended Test Cases for IE Testbench:

#### 1. **Stack Empty Detection** (HIGHEST PRIORITY)
```
Test: Operation on Empty Register
- FINIT (initialize)
- Execute FADD on empty ST(1)
- Expected: IE flag set, int_request asserted

Stack state:
  ST(0): empty (tag=11)  ← Critical: invalid operand access
  ST(1): empty (tag=11)
```

#### 2. **Signaling NaN (SNaN) Operation**
```
Test: SNaN operand triggers IE
- Load SNaN value (exponent=0x7FFF, high bit of mantissa=0)
- Execute arithmetic operation
- Expected: IE exception, result is QNaN

SNaN binary pattern for FP80:
  Exponent: 0x7FFF (all 1s)
  Integer bit: 0 (not set)
  Mantissa: any non-zero value
```

#### 3. **Invalid Arithmetic (Inf - Inf)**
```
Test: Infinity subtraction
- Load Inf and -Inf
- Execute: ST(0) = Inf, ST(1) = -Inf, FSUB
- Expected: Result is QNaN, IE set
```

#### 4. **Invalid Conversion**
```
Test: NaN to Integer conversion
- Load NaN
- Execute FISTP32 (store as 32-bit integer)
- Expected: Result = 0x80000000, IE set
```

#### 5. **Masked vs Unmasked IE**
```
Test A (Masked): IE disabled (bit 0 of control word = 1)
- Unmasked invalid operation
- Expected: NO int_request, only status flag set

Test B (Unmasked): IE enabled (bit 0 of control word = 0)
- Same invalid operation
- Expected: int_request asserted, exception_pending=1
```

### Verification Points:
```
Check these signals after invalid operation:
1. status_out[0] = 1 (IE flag set)
2. status_out[7] = 1 (ES - Exception Summary)
3. int_request = 1 (if unmasked)
4. tag_word_out shows register states
5. stack_ptr correct (not corrupted by exception)
```

---

## 7. CONTROL FLOW FOR IE EXCEPTION HANDLING

### Timeline for Unmasked IE:

```
Cycle N:    Arithmetic detects invalid condition
            → arith_invalid = 1

Cycle N+M:  Operation completes
            → exception_latch = 1 (in FPU_Core)
            
Cycle N+M+1:Exception Handler samples exception_latch
            → exception_invalid_latched ≤ 1 (sticky)
            
            Check if unmasked:
            → if (exception_invalid && !mask_invalid)
              → int_request ≤ 1
              
Cycle N+M+2:FPU_StatusWord samples status_invalid
            → exc_invalid ≤ 1 (bit 0)
            → exception_summary ≤ 1 (bit 7)
            
            Status word output updated:
            → status_out[0] = 1
            → status_out[7] = 1

INT remains asserted until:
            → FCLEX/FNCLEX instruction executed
            → exception_clear = 1
            → All latched exceptions cleared
            → int_request ≤ 0
```

### Control Word Effect:

```
If mask_invalid = 1 (IE masked - default):
  - Arithmetic still detects error
  - Exception flag still set in status word
  - INT NOT asserted (no interrupt)
  
If mask_invalid = 0 (IE unmasked):
  - Arithmetic detects error
  - Exception flag set in status word
  - INT asserted immediately
  - CPU must acknowledge via FCLEX
```

---

## 8. IMPLEMENTATION NOTES FOR IE TESTBENCHES

### Critical Signals to Monitor:
```
Input/Output:
  clk              → Clock source
  reset            → Synchronous reset (active HIGH)
  
Instruction Control:
  instruction      → 8-bit opcode
  execute          → Pulse to start execution
  ready            → Indicates FPU ready for next instruction
  
Data Interface:
  data_in[79:0]    → Input data (FP80 format)
  data_out[79:0]   → Output data after arithmetic
  
Exception Monitoring:
  int_request      → Exception interrupt output (active HIGH)
  error            → Composite error flag
  
Status/Control:
  status_out[15:0] → Status word output
  control_in[15:0] → Control word input
  tag_word_out[15:0] → Tag word (register states)
  
Stack Info:
  status_out[13:11] → Stack pointer (TOP)
```

### Testbench Design Pattern:
```
For each IE test case:
1. Initialize FPU (FINIT)
2. Set control word (FLDCW) - set IE mask as needed
3. Load test operands (FLD instructions)
4. Execute operation that triggers IE
5. Wait for ready signal
6. Check status_out[0] = IE bit set
7. Verify int_request state (depends on mask)
8. Clear exceptions (FCLEX)
9. Verify int_request cleared
10. Report PASS/FAIL
```

---

## FILES REFERENCE

### Core Exception Files:
- `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_Exception_Handler.v` (204 lines)
- `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_StatusWord.v` (154 lines)
- `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_RegisterStack.v` (222 lines)

### FPU Core Integration:
- `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_Core.v` (main module, ~1000+ lines)
- `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_ControlWord.v` (91 lines)
- `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_ArithmeticUnit.v` (complex module)

### Testbench Files:
- `/home/user/MyPC2/modelsim/fpu_core_tb.sv` (466 lines) - Primary reference
- `/home/user/MyPC2/modelsim/run_fpu_core_test.sh` (85 lines) - Test script
- `/home/user/MyPC2/modelsim/fpu_format_converter_tb.sv` - Alternate example

### Supporting:
- `/home/user/MyPC2/Quartus/rtl/FPU8087/tagRegister.v` (46 lines)
- `/home/user/MyPC2/Quartus/rtl/FPU8087/8087Status.v` (46 lines) - Alternative
- `/home/user/MyPC2/Quartus/rtl/FPU8087/StackRegister.v` (40 lines)

