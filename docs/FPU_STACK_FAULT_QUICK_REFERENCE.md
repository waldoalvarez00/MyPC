# FPU Stack Fault Implementation - Quick Reference Guide

## Signal Quick Reference

### Tag Word Encoding
```
tag_word[15:14] = ST(7) tag  │  tag_word[13:12] = ST(6) tag  │ ... │  tag_word[1:0] = ST(0) tag
│ 00 = Valid  │  01 = Zero  │  10 = Special  │  11 = Empty │
```

### Check if Register is Empty
```verilog
wire st0_empty = (tag_word[1:0] == 2'b11);
wire sti_empty = (tag_word[(i*2)+1:(i*2)] == 2'b11);
```

### Check if Register is Valid (Non-Empty)
```verilog
wire st0_valid = (tag_word[1:0] != 2'b11);
```

---

## Core Signal Locations (FPU_Core.v)

| **Item** | **Type** | **Line(s)** | **Use** |
|---------|---------|----------|--------|
| `tag_word` | wire [15:0] | 177, 351 | Read register validity |
| `stack_pointer` | wire [2:0] | 176, 203 | Stack top pointer (not typically needed) |
| `stack_overflow` | wire | 178, 205 | Push into non-empty ST(7) |
| `stack_underflow` | wire | 178, 205 | Pop from empty ST(0) |
| `status_stack_fault` | reg | 252, 2855 | SET when SF condition detected |
| `status_c1` | reg | 248, 260 | SET to 1 for overflow, 0 for underflow |
| `status_invalid` | reg | 250 | SET when empty operand + C1 behavior |
| `preop_invalid` | reg | 1040 | Use pattern for pre-op checking |
| `preop_nan_detected` | reg | 1041 | Use pattern for pre-op checking |

---

## Implementation Patterns

### Pattern 1: Check for Empty Register Before Operation

**For binary operations (FADD, FSUB, FMUL, FDIV):**
```verilog
wire st0_empty = (tag_word[1:0] == 2'b11);
wire sti_empty = (tag_word[(stack_index*2)+1:(stack_index*2)] == 2'b11);

if (st0_empty || sti_empty) begin
    status_stack_fault <= 1'b1;  // SF = 1
    status_c1 <= 1'b0;            // C1 = 0 (underflow)
    status_invalid <= 1'b1;       // IE = 1
    error <= !mask_invalid;
    temp_result <= 80'h7FFF_C000_0000_0000_0000;  // QNaN
    state <= STATE_WRITEBACK;
end
```

### Pattern 2: Check Before Push (Load Operations)

**For FLD, FILD, FBLD, etc.:**
```verilog
wire st7_empty = (tag_word[15:14] != 2'b11);  // Will push overflow
wire will_overflow = st7_empty;  // Inverted logic: non-empty = overflow

if (will_overflow) begin
    status_stack_fault <= 1'b1;  // SF = 1
    status_c1 <= 1'b1;            // C1 = 1 (overflow)
    // Option A: Return QNaN without pushing
    temp_result <= 80'h7FFF_C000_0000_0000_0000;
    state <= STATE_WRITEBACK;
    // Option B: Don't set stack_push, just return error
end else begin
    stack_push <= 1'b1;
    // ... normal push operation
end
```

### Pattern 3: Check Before Pop

**For FSTP, FCOMPP, etc.:**
```verilog
wire st0_empty = (tag_word[1:0] == 2'b11);

if (st0_empty) begin
    status_stack_fault <= 1'b1;  // SF = 1
    status_c1 <= 1'b0;            // C1 = 0 (underflow)
    status_invalid <= 1'b1;       // IE = 1
    error <= !mask_invalid;
    // Don't perform pop
    state <= STATE_DONE;
end else begin
    stack_pop <= 1'b1;
    // ... normal pop operation
end
```

### Pattern 4: Extract Tag Bits (Helper Function)

```verilog
function automatic [1:0] get_tag;
    input [15:0] tw;
    input [2:0] idx;  // 0=ST(0), 1=ST(1), ..., 7=ST(7)
    begin
        get_tag = tw[(idx*2)+1:(idx*2)];
    end
endfunction

// Usage:
wire [1:0] st3_tag = get_tag(tag_word, 3'd3);
wire st3_empty = (st3_tag == 2'b11);
```

---

## State Diagram Modifications

### Current Flow (INCORRECT)
```
STATE_IDLE → STATE_DECODE → STATE_EXECUTE → STATE_WRITEBACK → STATE_DONE
                                                                    │
                                                    (set SF after operation)
```

### Recommended Flow (with pre-op checks)
```
STATE_IDLE → STATE_DECODE → [PRE-CHECK] → STATE_EXECUTE → STATE_WRITEBACK → STATE_DONE
                                │
                                ├─ Stack full? → SF=1, C1=1, return QNaN
                                ├─ ST(0) empty? → SF=1, C1=0, IE=1, return QNaN
                                ├─ ST(i) empty? → SF=1, C1=0, IE=1, return QNaN
                                └─ OK? → Continue to STATE_EXECUTE
```

---

## Key Code Sections to Modify

### Section 1: Load Operations (FLD, FILD, FBLD, etc.)
- **Location:** FPU_Core.v, line ~2670-2690
- **Action:** Add pre-push overflow check

### Section 2: Binary Operations (FADD, FSUB, FMUL, FDIV, etc.)
- **Location:** FPU_Core.v, lines ~1278-1500
- **Action:** Add pre-operation empty check before arith_enable

### Section 3: Pop Operations (FSTP, FCOMPP, etc.)
- **Location:** FPU_Core.v, lines ~2800-2820
- **Action:** Add pre-pop underflow check

### Section 4: Transcendental Operations (FSIN, FCOS, etc.)
- **Location:** FPU_Core.v, lines ~1600-1800
- **Action:** Add check for empty ST(0)

---

## C1 Flag Rule

```
SF=1, C1=0  →  Stack Underflow (not enough operands)
SF=1, C1=1  →  Stack Overflow (all 8 registers full)
SF=0        →  No stack fault
```

---

## Testing Checklist

- [ ] Pre-push overflow check (FLD when stack full)
- [ ] Pre-pop underflow check (FSTP when ST(0) empty)
- [ ] Pre-op empty check (FADD when ST(0) or ST(1) empty)
- [ ] C1 flag set correctly (1 for overflow, 0 for underflow)
- [ ] SF persists in status word until FCLEX
- [ ] No interference with exception masking
- [ ] Unmasked IE still blocks operation if configured

---

## 8087 Compliance Notes

1. **Stack Fault is NOT an exception** - It doesn't trigger INT signal
2. **Stack Fault is NOT masked** - SF flag always sets in status word
3. **Invalid Operation may be masked** - If IE is masked, operation may return QNaN and continue
4. **C1 is used for overflow/underflow distinction** - Not for comparison condition codes
5. **Push/Pop operations are atomic** - Either fully execute or fully fault, no partial updates

