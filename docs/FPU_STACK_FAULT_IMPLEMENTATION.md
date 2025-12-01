# FPU Stack Fault Implementation Analysis

## Executive Summary

This document provides a detailed analysis of how stack fault checking can be implemented in the FPU8087. The FPU currently detects stack overflow/underflow at the RegisterStack level but does not validate stack state before operations or set condition codes (C1) for overflow vs. underflow.

---

## 1. FPU_RegisterStack.v - Stack Tag Management

### 1.1 Tag Word Format and Storage

**File:** `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_RegisterStack.v`

**Tag Values (lines 14-18):**
```verilog
// 00 = Valid (non-zero)
// 01 = Zero
// 10 = Special (NaN, Infinity, Denormal)
// 11 = Empty
```

**Tag Storage (lines 61):**
```verilog
reg [1:0]  tags [0:7];              // Tag for each register (individual tags)
```

**Tag Word Output (lines 210-219):**
```verilog
tag_word = {
    tags[physical_reg(3'd7)],
    tags[physical_reg(3'd6)],
    tags[physical_reg(3'd5)],
    tags[physical_reg(3'd4)],
    tags[physical_reg(3'd3)],
    tags[physical_reg(3'd2)],
    tags[physical_reg(3'd1)],
    tags[physical_reg(3'd0)]
};
```

**Key Signal Names:**
- `tag_word` - 16-bit output, bits assembled as: [15:14]=ST(7), [13:12]=ST(6), ... [1:0]=ST(0)
- Each register's tag occupies 2 bits in the tag word

### 1.2 Physical to Logical Register Mapping

**Physical Register Calculation (lines 97-102):**
```verilog
function [2:0] physical_reg;
    input [2:0] logical_reg;
    begin
        physical_reg = (stack_ptr + logical_reg) & 3'b111;
    end
endfunction
```

**Usage:**
- `stack_ptr` is the Stack Top Pointer (0-7, rotates through 8 registers)
- `logical_reg` is ST(0)=0, ST(1)=1, ST(2)=2, etc.
- Physical address = (TOP + logical_index) mod 8

### 1.3 Empty Register Detection

To check if a register is empty (tag = 2'b11):

1. **Extract tag bits for a specific logical register:**
   ```verilog
   // For logical register i (ST(i))
   wire [1:0] register_tag = tag_word[(i*2)+1:(i*2)];
   
   // Check if empty
   wire is_empty = (register_tag == 2'b11);
   ```

2. **Example for ST(0) (bits [1:0]):**
   ```verilog
   wire st0_tag = tag_word[1:0];
   wire st0_empty = (st0_tag == 2'b11);
   ```

3. **Example for ST(1) (bits [3:2]):**
   ```verilog
   wire st1_tag = tag_word[3:2];
   wire st1_empty = (st1_tag == 2'b11);
   ```

### 1.4 Stack Overflow/Underflow Signals

**Stack Overflow Detection (lines 141-144):**
```verilog
// Check for overflow (pushing into non-empty slot)
if (tags[(new_stack_ptr + 3'd7) & 3'b111] != 2'b11) begin
    stack_overflow <= 1'b1;
end
```

**Stack Underflow Detection (lines 146-149):**
```verilog
// Check for underflow (popping from empty slot)
if (tags[physical_reg(3'd0)] == 2'b11) begin
    stack_underflow <= 1'b1;
end
```

**Output Signals:**
- `stack_overflow` - Active when push operation tries to overwrite non-empty register
- `stack_underflow` - Active when pop operation reads from empty register

---

## 2. FPU_Core.v - Operand Checking and Stack Fault Integration

### 2.1 Stack Fault Signal Connections

**File:** `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_Core.v`

**Lines 176-178 (Stack connections):**
```verilog
wire [2:0]  stack_pointer;
wire [15:0] tag_word;
wire        stack_overflow, stack_underflow;
```

**Line 177 - Tag word output:**
```verilog
wire [15:0] tag_word;
```

**Assignment to output (line 351):**
```verilog
assign tag_word_out = tag_word;
```

### 2.2 Status Word Stack Fault Field

**Stack Fault Status (line 252):**
```verilog
reg        status_stack_fault;
```

**FPU_StatusWord instantiation (lines 254-274):**
```verilog
FPU_StatusWord status_word (
    .clk(clk),
    .reset(reset),
    .stack_ptr(stack_pointer),
    .c3(status_c3),
    .c2(status_c2),
    .c1(status_c1),
    .c0(status_c0),
    .cc_write(status_cc_write),
    .invalid(status_invalid),
    .denormal(status_denormal),
    .zero_divide(status_zero_div),
    .overflow(status_overflow),
    .underflow(status_underflow),
    .precision(status_precision),
    .stack_fault(status_stack_fault),  // <-- SF input
    .clear_exceptions(status_clear_exc),
    .set_busy(status_set_busy),
    .clear_busy(status_clear_busy),
    .status_word(status_out)
);
```

### 2.3 Stack Fault Status Setting

**Lines 2850-2863 (STATE_DONE):**
```verilog
STATE_DONE: begin
    ready <= 1'b1;
    status_clear_busy <= 1'b1;
    status_stack_fault <= stack_overflow | stack_underflow;  // <-- SET HERE
    
    // Check for unmasked exceptions
    error <= (status_invalid & ~mask_invalid) |
            (status_denormal & ~mask_denormal) |
            (status_zero_div & ~mask_zero_div) |
            (status_overflow & ~mask_overflow) |
            (status_underflow & ~mask_underflow) |
            (status_precision & ~mask_precision);
    
    arith_operation <= 5'd15;
    state <= STATE_IDLE;
end
```

**Current Implementation Issue:**
- Stack overflow/underflow is checked AFTER the operation (in STATE_DONE)
- No pre-operation validation for empty operands

### 2.4 Pre-Operation Validation Framework

**Pre-operation variables (lines 1040-1041):**
```verilog
reg       preop_invalid;            // Pre-operation invalid operation detected
reg       preop_nan_detected;       // Pre-operation NaN detected
```

**Example usage in FADD (lines 1278-1299):**
```verilog
INST_FADD, INST_FADDP: begin
    if (~arith_done) begin
        if (~arith_enable) begin
            // Pre-operation checks
            preop_nan_detected <= is_nan(temp_operand_a) || is_nan(temp_operand_b);
            preop_invalid <= is_invalid_add_sub(temp_operand_a, temp_operand_b, 1'b0);
            
            if (preop_nan_detected || preop_invalid) begin
                // Short-circuit: return NaN immediately
                temp_result <= propagate_nan(temp_operand_a, temp_operand_b, 1'b1);
                if (preop_nan_detected && (is_snan(temp_operand_a) || is_snan(temp_operand_b)))
                    status_invalid <= 1'b1;
                else if (preop_invalid)
                    status_invalid <= 1'b1;
                error <= !mask_invalid;
                state <= STATE_WRITEBACK;
            end else begin
                // Normal operation
                arith_operation <= 4'd0;  // OP_ADD
                // ... rest of operation
            end
        end
    end
end
```

### 2.5 Stack Pointer and Tag Word Access in FPU_Core

**Stack pointer wire (line 176):**
```verilog
wire [2:0]  stack_pointer;
```

**Connected from register stack (line 203):**
```verilog
.stack_ptr(stack_pointer),
```

**Tag word extraction helper function (to be added):**
```verilog
// Helper function to extract tag for a logical register
function automatic [1:0] get_register_tag;
    input [15:0] tag_word;
    input [2:0]  logical_index;  // 0 for ST(0), 1 for ST(1), etc.
    begin
        get_register_tag = tag_word[(logical_index * 2) + 1 : (logical_index * 2)];
    end
endfunction
```

---

## 3. FPU_Exception_Handler.v - Exception Handling

### 3.1 Stack Fault Is Not Handled by Exception Handler

**File:** `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_Exception_Handler.v`

**Current Exception Types (lines 37-42):**
```verilog
input wire exception_invalid,
input wire exception_denormal,
input wire exception_zero_div,
input wire exception_overflow,
input wire exception_underflow,
input wire exception_precision,
```

**Notable:** There is NO `exception_stack_fault` input to the exception handler.

**Exception latching (lines 150-172):**
```verilog
end else if (exception_latch) begin
    // Operation completed - latch any exceptions
    exception_invalid_latched   <= exception_invalid_latched   || exception_invalid;
    exception_denormal_latched  <= exception_denormal_latched  || exception_denormal;
    exception_zero_div_latched  <= exception_zero_div_latched  || exception_zero_div;
    exception_overflow_latched  <= exception_overflow_latched  || exception_overflow;
    exception_underflow_latched <= exception_underflow_latched || exception_underflow;
    exception_precision_latched <= exception_precision_latched || exception_precision;
    
    // 8087 Behavior: INT asserts when an unmasked exception OCCURS
    if ((exception_invalid   && !mask_invalid)   ||
        (exception_denormal  && !mask_denormal)  ||
        (exception_zero_div  && !mask_zero_div)  ||
        (exception_overflow  && !mask_overflow)  ||
        (exception_underflow && !mask_underflow) ||
        (exception_precision && !mask_precision)) begin
        int_request <= 1'b1;
        exception_pending <= 1'b1;
    end
end
```

### 3.2 Stack Fault Is Separate from Exception Handler

**Why:** Stack Fault is handled directly in FPU_StatusWord and FPU_Core
- Set as: `status_stack_fault <= stack_overflow | stack_underflow;` (line 2855 in FPU_Core.v)
- NOT part of exception priority system
- NOT masked by exception masks
- Does NOT trigger INT signal

---

## 4. FPU_StatusWord.v - Status Word Assembly

### 4.1 Stack Fault Status Bit

**File:** `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_StatusWord.v`

**Status Word Format (lines 9-23):**
```
[15]    : Busy (B)
[14]    : Condition Code C3
[13:11] : Stack Top Pointer
[10]    : Condition Code C2
[9]     : Condition Code C1
[8]     : Condition Code C0
[7]     : Exception Summary (ES)
[6]     : Stack Fault (SF)
[5]     : Precision Exception (PE)
[4]     : Underflow Exception (UE)
[3]     : Overflow Exception (OE)
[2]     : Zero Divide Exception (ZE)
[1]     : Denormalized Operand Exception (DE)
[0]     : Invalid Operation Exception (IE)
```

**Exception Summary Calculation (lines 72-74):**
```verilog
wire exception_summary;
assign exception_summary = exc_invalid | exc_denormal | exc_zero_div |
                           exc_overflow | exc_underflow | exc_precision;
```

**Important:** Stack Fault (SF) bit is NOT included in Exception Summary!

### 4.2 Status Word Assembly (lines 135-152)

```verilog
always @(*) begin
    status_word = {
        busy,               // [15] Busy
        cond_c3,            // [14] C3
        stack_ptr,          // [13:11] Stack pointer
        cond_c2,            // [10] C2
        cond_c1,            // [9] C1
        cond_c0,            // [8] C0
        exception_summary,  // [7] Exception summary
        exc_stack_fault,    // [6] Stack fault
        exc_precision,      // [5] Precision
        exc_underflow,      // [4] Underflow
        exc_overflow,       // [3] Overflow
        exc_zero_div,       // [2] Zero divide
        exc_denormal,       // [1] Denormalized
        exc_invalid         // [0] Invalid
    };
end
```

**Stack Fault Sticky Flag (lines 126):**
```verilog
if (stack_fault) exc_stack_fault <= 1'b1;
```

---

## 5. Key Signal Names and Locations for Implementation

### Summary Table

| **Aspect** | **Signal/Variable** | **File** | **Line(s)** |
|-----------|------------------|---------|-----------|
| Tag word output | `tag_word` | FPU_Core.v | 177, 351 |
| Empty register check | `(tag_word[...] == 2'b11)` | N/A - derived | - |
| Stack overflow | `stack_overflow` | FPU_Core.v | 178, 205 |
| Stack underflow | `stack_underflow` | FPU_Core.v | 178, 205 |
| Stack pointer | `stack_pointer` | FPU_Core.v | 176, 203 |
| Status SF field | `status_stack_fault` | FPU_Core.v | 252, 2855 |
| Condition code C1 | `status_c1` | FPU_Core.v | 248, 260 |
| Pre-operation checks | `preop_invalid`, `preop_nan_detected` | FPU_Core.v | 1040-1041 |
| STATE_DECODE operands | `temp_operand_a`, `temp_operand_b` | FPU_Core.v | 1223-1224 |
| STATE_EXECUTE start | FADD example | FPU_Core.v | 1278-1299 |
| STATE_DONE finalize | Stack fault set | FPU_Core.v | 2852-2870 |

---

## 6. Implementation Points for Stack Fault Checking

### 6.1 PRE-PUSH Overflow Checking (for FLD, FILD, FBLD, etc.)

**Location:** FPU_Core.v, STATE_EXECUTE, before `stack_push <= 1'b1`

**Current Problem:** Load operations don't check if push will overflow before setting push signal.

**Lines where loads execute (2677-2690):**
```verilog
// Load operations: push result onto stack
if (state == STATE_WRITEBACK) begin
    stack_push <= 1'b1;
    stack_write_reg <= 3'd0;
    stack_data_in <= temp_result;
    stack_write_enable <= 1'b1;
end
```

**Required Addition:**
```verilog
// Check if ST(7) is non-empty (would cause overflow)
wire will_overflow = (tag_word[15:14] != 2'b11);  // Physical ST(7) corresponds to bits [15:14]

if (will_overflow) begin
    status_stack_fault <= 1'b1;
    status_c1 <= 1'b1;  // C1=1 for overflow
    // Return QNaN instead of pushing
    // OR block the push with unmasked exception
end else begin
    stack_push <= 1'b1;
    // ... normal operation
end
```

### 6.2 PRE-OPERATION Empty Operand Checking (for binary operations)

**Location:** FPU_Core.v, STATE_DECODE or early STATE_EXECUTE

**Current:** Operations assume operands are valid

**For FADD, FSUB, FMUL, FDIV (requires two operands):**
```verilog
// Extract tag for ST(0) and ST(i)
wire [1:0] st0_tag = tag_word[1:0];
wire [1:0] sti_tag = tag_word[(stack_index * 2) + 1 : (stack_index * 2)];

wire st0_empty = (st0_tag == 2'b11);
wire sti_empty = (sti_tag == 2'b11);

if (st0_empty || sti_empty) begin
    // Stack underflow (insufficient operands)
    status_stack_fault <= 1'b1;
    status_c1 <= 1'b0;  // C1=0 for underflow
    status_invalid <= 1'b1;
    error <= !mask_invalid;
    state <= STATE_WRITEBACK;  // Skip to end with QNaN
end
```

### 6.3 Pre-Pop Underflow Checking

**Location:** FPU_Core.v, before any `stack_pop <= 1'b1`

**For FSTP, FCOMPP, etc. (pop operations):**
```verilog
// Check if ST(0) is empty before allowing pop
wire st0_empty = (tag_word[1:0] == 2'b11);

if (st0_empty) begin
    status_stack_fault <= 1'b1;
    status_c1 <= 1'b0;  // C1=0 for underflow
    // Don't pop, return to ready state
end else begin
    stack_pop <= 1'b1;
    // ... normal operation
end
```

### 6.4 Condition Code C1 Assignment

**Line 248 in FPU_Core.v:**
```verilog
reg        status_cc_write;
reg        status_c3, status_c2, status_c1, status_c0;
```

**Set C1 based on overflow vs. underflow:**
```verilog
// C1 = 1 for overflow (stack full on push)
// C1 = 0 for underflow (stack empty on pop)
if (stack_overflow) begin
    status_stack_fault <= 1'b1;
    status_c1 <= 1'b1;
end else if (stack_underflow) begin
    status_stack_fault <= 1'b1;
    status_c1 <= 1'b0;
end
```

---

## 7. Flow for Pre-Operation Stack Fault Checking

### 7.1 Recommended Architecture

```
STATE_IDLE
    ↓
STATE_DECODE
    ↓ (capture operands and check stack state)
    ├─→ [Check pre-conditions]
    │   ├─→ [For loads] Is ST(7) empty? If not → SF
    │   ├─→ [For binary ops] Are ST(0) and ST(i) valid? If not → SF+IE
    │   ├─→ [For pops] Is ST(0) empty? If not → SF
    │   └─→ [For FINCSTP/FDECSTP] N/A (no validation needed)
    │
    └─→ [If pre-conditions fail]
        └─→ STATE_DONE (return error/QNaN)
        
    └─→ [If pre-conditions OK]
        └─→ STATE_EXECUTE (normal operation)
```

### 7.2 Integration with Exception Masking

**Key Insight:** Stack Fault is not maskable like Invalid Operation

- SF always sets in status word
- But operation may still proceed if IE (Invalid) is masked
- Set both SF and IE when empty operand is detected
- C1 indicates overflow (1) vs. underflow (0)

---

## 8. Test Cases for Implementation

### Test 1: Pre-Push Overflow
```
1. Fill all 8 stack positions
2. Execute FLD 1.0 (push)
3. Expected: SF=1, C1=1, result=QNaN (if IE masked)
```

### Test 2: Pre-Pop Underflow  
```
1. Pop all stack entries
2. Execute FSTP (pop from empty)
3. Expected: SF=1, C1=0, no value popped
```

### Test 3: Binary Operation with Empty Operand
```
1. Clear ST(0) with FFREE
2. Execute FADD ST(0), ST(1)
3. Expected: SF=1, IE=1, C1=0, result=QNaN
```

### Test 4: Overflow/Underflow Distinction
```
Compare C1 flag value:
- SF=1, C1=1 → Overflow
- SF=1, C1=0 → Underflow
```

---

## 9. References

### Key Files
- **Tag word logic:** `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_RegisterStack.v` (lines 210-219)
- **Status word assembly:** `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_StatusWord.v` (lines 135-152)
- **Core integration:** `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_Core.v` (lines 1278-2870)
- **Exception handling:** `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_Exception_Handler.v`

### 8087 Reference Material
- Stack Fault (SF) - Status word bit 6
- Condition code C1 - Used for overflow/underflow distinction
- Invalid Operation (IE) - Combined with SF for empty operands
- Not affected by exception masks

