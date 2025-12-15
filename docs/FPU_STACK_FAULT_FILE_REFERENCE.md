# FPU Stack Fault - File Reference and Key Locations

## Overview
This document serves as a master index for all files involved in stack fault implementation, with exact line numbers and signal names.

---

## 1. FPU_RegisterStack.v
**Path:** `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_RegisterStack.v`  
**Lines:** 223 total  
**Purpose:** 8-register stack with tag tracking

### Key Signals
| Signal | Type | Lines | Purpose |
|--------|------|-------|---------|
| `tags[0:7]` | reg [1:0] [0:7] | 61 | Individual register tags |
| `tag_word` | reg [15:0] | 49 | Assembled 16-bit tag word |
| `stack_ptr` | reg [2:0] | 46 | Stack pointer (0-7) |
| `stack_overflow` | reg | 52 | Push overflow flag |
| `stack_underflow` | reg | 53 | Pop underflow flag |

### Key Functions
| Function | Lines | Returns | Use |
|----------|-------|---------|-----|
| `generate_tag()` | 69-91 | [1:0] | Derive tag from value |
| `physical_reg()` | 97-102 | [2:0] | Map logical to physical register |

### Tag Word Assembly (IMPORTANT)
**Lines 210-219:**
```verilog
tag_word = {
    tags[physical_reg(3'd7)],  // [15:14]
    tags[physical_reg(3'd6)],  // [13:12]
    tags[physical_reg(3'd5)],  // [11:10]
    tags[physical_reg(3'd4)],  // [9:8]
    tags[physical_reg(3'd3)],  // [7:6]
    tags[physical_reg(3'd2)],  // [5:4]
    tags[physical_reg(3'd1)],  // [3:2]
    tags[physical_reg(3'd0)]   // [1:0]
};
```

### Stack Fault Detection
| Condition | Lines | Trigger |
|-----------|-------|---------|
| Overflow (push non-empty ST(7)) | 141-144 | `stack_overflow <= 1'b1` |
| Underflow (pop empty ST(0)) | 146-149 | `stack_underflow <= 1'b1` |

---

## 2. FPU_Core.v
**Path:** `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_Core.v`  
**Lines:** 2877 total  
**Purpose:** Top-level FPU control and instruction sequencing

### Wire Connections from RegisterStack
| Signal | Line | Direction | Use |
|--------|------|-----------|-----|
| `tag_word` | 177, 351 | output wire | Export to outside |
| `stack_pointer` | 176, 203 | input wire | Stack top pointer |
| `stack_overflow` | 178, 205 | input wire | Detects push overflow |
| `stack_underflow` | 178, 205 | input wire | Detects pop underflow |

### Status Registers for Stack Fault
| Register | Line | Bits | Purpose |
|----------|------|------|---------|
| `status_stack_fault` | 252 | 1 | SF flag (set in STATE_DONE) |
| `status_c1` | 248 | 1 | Condition code 1 (1=overflow, 0=underflow) |
| `status_invalid` | 250 | 1 | IE flag (combined with SF) |

### FPU_StatusWord Instantiation
**Lines 254-274:**
```verilog
FPU_StatusWord status_word (
    .stack_ptr(stack_pointer),         // Line 257
    .stack_fault(status_stack_fault),  // Line 269 - INPUT
    .status_word(status_out)           // Line 273 - OUTPUT
);
```

### Pre-Operation Check Variables
| Variable | Line | Type | Purpose |
|----------|------|------|---------|
| `preop_invalid` | 1040 | reg | Pre-op invalid detection |
| `preop_nan_detected` | 1041 | reg | Pre-op NaN detection |

### State Machine States (Relevant Lines)
| State | Lines | Purpose |
|-------|-------|---------|
| STATE_IDLE | 1014 | Wait for instruction |
| STATE_DECODE | 1015, 1221-1273 | Decode and capture operands |
| STATE_EXECUTE | 1016, 1275-2695 | Execute instruction |
| STATE_WRITEBACK | 1017, 2696-2825 | Write result back |
| STATE_DONE | 1018, 2852-2870 | **SET SF HERE** |

### STATE_EXECUTE - Binary Operations
| Instruction | Lines | Pre-op Check Pattern |
|-------------|-------|---------------------|
| FADD, FADDP | 1278-1299 | NaN+invalid check (use as template) |
| FSUB, FSUBP | 1348-1369 | NaN+invalid check |
| FMUL, FMULP | 1397-1418 | NaN+invalid check |
| FDIV, FDIVP | 1446-1467 | NaN+invalid check |

**Example Pattern (FADD at line 1283-1299):**
```verilog
// Pre-operation checks
preop_nan_detected <= is_nan(temp_operand_a) || is_nan(temp_operand_b);
preop_invalid <= is_invalid_add_sub(temp_operand_a, temp_operand_b, 1'b0);

if (preop_nan_detected || preop_invalid) begin
    // Short-circuit: return NaN immediately
    temp_result <= propagate_nan(temp_operand_a, temp_operand_b, 1'b1);
    if (preop_nan_detected && (is_snan(...) || is_snan(...)))
        status_invalid <= 1'b1;
    else if (preop_invalid)
        status_invalid <= 1'b1;
    error <= !mask_invalid;
    state <= STATE_WRITEBACK;
end else begin
    // Normal operation
    arith_operation <= 4'd0;  // OP_ADD
    // ... enable arithmetic unit
end
```

### STATE_EXECUTE - Load Operations
| Instruction | Lines | Stack Action |
|-------------|-------|--------------|
| FLD, FILD, FBLD, FLD32, FLD64 | ~2670-2700 | `stack_push <= 1'b1` |

**Lines 2677-2690 (Current - No Overflow Check):**
```verilog
// Load operations: push result onto stack
if (state == STATE_WRITEBACK) begin
    stack_push <= 1'b1;
    stack_write_reg <= 3'd0;
    stack_data_in <= temp_result;
    stack_write_enable <= 1'b1;
end
```

### STATE_EXECUTE - Pop Operations
| Instruction | Lines | Stack Action |
|-------------|-------|--------------|
| FSTP, FCOMPP, FCOMPM | ~2800-2820 | `stack_pop <= 1'b1` |

**Example at lines 2814-2817:**
```verilog
// Compare and pop twice
stack_pop <= 1'b1;
// Second pop will be handled by setting a flag
```

### STATE_DONE - Stack Fault Setting
**Lines 2852-2870 (CRITICAL):**
```verilog
STATE_DONE: begin
    ready <= 1'b1;
    status_clear_busy <= 1'b1;
    status_stack_fault <= stack_overflow | stack_underflow;  // <-- LINE 2855
    
    // Check for unmasked exceptions (lines 2858-2863)
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

### Operand Capture (STATE_DECODE)
**Lines 1223-1224:**
```verilog
temp_operand_a <= st0;              // ST(0)
temp_operand_b <= stack_read_data;  // ST(i)
```

### Stack Operation Signals
| Signal | Line | Use |
|--------|------|-----|
| `stack_push` | 180 | Request push operation |
| `stack_pop` | 180 | Request pop operation |
| `stack_data_in` | 181 | Data to push |
| `stack_write_reg` | 182 | Register index for write |
| `stack_write_enable` | 183 | Enable write |
| `stack_read_sel` | 184 | Register index for read |
| `stack_inc_ptr` | 185 | FINCSTP operation |
| `stack_dec_ptr` | 186 | FDECSTP operation |
| `stack_free_reg` | 187 | FFREE operation |
| `stack_free_index` | 188 | Register to free |
| `stack_init_stack` | 189 | FINIT operation |

---

## 3. FPU_StatusWord.v
**Path:** `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_StatusWord.v`  
**Lines:** 155 total  
**Purpose:** Status word register and assembly

### Input Signals (FPU_Core feeds these)
| Input | Lines | From | Purpose |
|-------|-------|------|---------|
| `stack_fault` | 47 | FPU_Core.status_stack_fault | SF input |
| `c1` | 36 | FPU_Core.status_c1 | Condition code input |
| `clear_exceptions` | 50 | FPU_Core.status_clear_exc | Clear all exception bits |

### Exception Latching
**Lines 110-127 (Exception stickiness):**
```verilog
if (clear_exceptions) begin
    exc_invalid <= 1'b0;
    // ... clear others ...
    exc_stack_fault <= 1'b0;
end else begin
    // Sticky exception flags (OR in new exceptions)
    // ... 
    if (stack_fault) exc_stack_fault <= 1'b1;
end
```

### Status Word Assembly
**Lines 135-152 (Output format):**
```verilog
status_word = {
    busy,               // [15] Busy
    cond_c3,            // [14] C3
    stack_ptr,          // [13:11] Stack pointer
    cond_c2,            // [10] C2
    cond_c1,            // [9] C1 <-- OUR FLAG
    cond_c0,            // [8] C0
    exception_summary,  // [7] ES (note: does NOT include SF)
    exc_stack_fault,    // [6] SF <-- OUR FLAG
    exc_precision,      // [5] PE
    exc_underflow,      // [4] UE
    exc_overflow,       // [3] OE
    exc_zero_div,       // [2] ZE
    exc_denormal,       // [1] DE
    exc_invalid         // [0] IE
};
```

**Important:** SF (line 144) is separate from exception_summary (line 143)

---

## 4. FPU_Exception_Handler.v
**Path:** `/home/user/MyPC2/Quartus/rtl/FPU8087/FPU_Exception_Handler.v`  
**Lines:** 204 total  
**Purpose:** Exception latching and INT signal generation

### Note on Stack Fault
**Lines 37-42 (Exception inputs - NO stack_fault input):**
```verilog
input wire exception_invalid,
input wire exception_denormal,
input wire exception_zero_div,
input wire exception_overflow,
input wire exception_underflow,
input wire exception_precision,
// NOTE: NO exception_stack_fault input!
```

**Key Insight:** Stack Fault is NOT part of the exception handler system. It's handled entirely in FPU_Core and FPU_StatusWord.

---

## 5. Summary of Modification Points

### To Add Stack Fault Checking, Modify FPU_Core.v:

1. **Lines ~1278-1500 (Binary Operations)**
   - Add empty register check for FADD, FSUB, FMUL, FDIV
   - Pattern: Extract tag bits, check for 2'b11, set SF+C1+IE if empty
   
2. **Lines ~2670-2690 (Load Operations)**
   - Add overflow check before stack_push
   - Pattern: Check ST(7) tag bits, set SF+C1 if non-empty
   
3. **Lines ~2800-2820 (Pop Operations)**
   - Add underflow check before stack_pop
   - Pattern: Check ST(0) tag bits, set SF+C1 if empty
   
4. **Lines ~1600-1800 (Unary Operations)**
   - Add ST(0) empty check for FSIN, FCOS, FSQRT, etc.
   - Pattern: Check ST(0) tag, set SF+C1+IE if empty

### Helper Function to Add (anywhere before STATE_DECODE):
```verilog
function automatic [1:0] get_tag;
    input [15:0] tag_word;
    input [2:0] logical_index;
    begin
        get_tag = tag_word[(logical_index * 2) + 1 : (logical_index * 2)];
    end
endfunction
```

---

## 6. Tag Bit Extraction Cheat Sheet

```verilog
// Extract tag for logical register i (0-7)
wire [1:0] tag_i = tag_word[(i*2)+1:(i*2)];

// ST(0) - bits [1:0]
wire [1:0] st0_tag = tag_word[1:0];

// ST(1) - bits [3:2]
wire [1:0] st1_tag = tag_word[3:2];

// ST(2) - bits [5:4]
wire [1:0] st2_tag = tag_word[5:4];

// ST(3) - bits [7:6]
wire [1:0] st3_tag = tag_word[7:6];

// ST(4) - bits [9:8]
wire [1:0] st4_tag = tag_word[9:8];

// ST(5) - bits [11:10]
wire [1:0] st5_tag = tag_word[11:10];

// ST(6) - bits [13:12]
wire [1:0] st6_tag = tag_word[13:12];

// ST(7) - bits [15:14]
wire [1:0] st7_tag = tag_word[15:14];

// Check if register is empty
wire empty = (tag == 2'b11);
```

---

## 7. Test Points

### Test File Locations
- Testbenches: `/home/user/MyPC2/Quartus/rtl/FPU8087/tests/`
- Test runner: `/home/user/MyPC2/Quartus/rtl/FPU8087/run_all_tests.sh`

### Key Test Scenarios
1. **Overflow Test:** Fill all 8 registers, execute FLD
2. **Underflow Test:** Empty stack, execute FSTP or FADD
3. **C1 Flag Test:** Verify C1=1 for overflow, C1=0 for underflow
4. **Persistence Test:** Verify SF persists until FCLEX

---

## 8. Cross-Reference: From Task to Implementation

| Task | File | Lines | Signal | Action |
|------|------|-------|--------|--------|
| Check if ST(0) empty | FPU_Core.v | ~1280 | tag_word[1:0] | Read and compare == 2'b11 |
| Check if ST(i) empty | FPU_Core.v | ~1280 | tag_word[(i*2)+1:i*2] | Read and compare == 2'b11 |
| Check pre-push overflow | FPU_Core.v | ~2680 | tag_word[15:14] | Read and check != 2'b11 |
| Set SF flag | FPU_Core.v | 252, 2855 | status_stack_fault | Assign 1'b1 |
| Set C1 for overflow | FPU_Core.v | 248 | status_c1 | Assign 1'b1 |
| Set C1 for underflow | FPU_Core.v | 248 | status_c1 | Assign 1'b0 |
| Export SF in status word | FPU_StatusWord.v | 144 | status_word[6] | Automatic via assembly |

