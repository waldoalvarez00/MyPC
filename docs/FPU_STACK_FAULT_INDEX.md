# FPU Stack Fault Implementation - Document Index

## Overview

This folder contains comprehensive analysis for implementing stack fault (SF) checking in the FPU8087. Three complementary documents provide different levels of detail.

---

## Documents

### 1. **FPU_STACK_FAULT_IMPLEMENTATION.md** (Main Technical Reference)
**Use this when:** You need detailed understanding of how stack faults work

**Contains:**
- Section 1: FPU_RegisterStack.v - Tag word storage and access
- Section 2: FPU_Core.v - Signal connections and status word integration
- Section 3: FPU_Exception_Handler.v - Why stack faults are separate from exceptions
- Section 4: FPU_StatusWord.v - How SF flag is assembled
- Section 5: Key signal names and locations (summary table)
- Section 6: Implementation patterns for pre-operation checking
- Section 7: Recommended architecture and flow diagrams
- Section 8: Test cases with expected results
- Section 9: File references and documentation

**Key Sections:**
- Lines 44-222: FPU_RegisterStack.v analysis
- Lines 235-351: FPU_Core.v signal connections and status word
- Lines 364-401: FPU_Exception_Handler.v analysis
- Lines 414-459: FPU_StatusWord.v assembly
- Lines 472-538: Implementation points for modifications

---

### 2. **FPU_STACK_FAULT_QUICK_REFERENCE.md** (Developer Guide)
**Use this when:** You're actively coding and need quick patterns

**Contains:**
- Signal Quick Reference (tag word encoding and how to check for empty)
- Core Signal Locations (table of all signals in FPU_Core.v)
- Implementation Patterns (copy-paste ready code)
  - Pattern 1: Check for empty register before operation
  - Pattern 2: Check before push (load operations)
  - Pattern 3: Check before pop
  - Pattern 4: Extract tag bits (helper function)
- State Diagram Modifications (current vs. recommended flow)
- Key Code Sections to Modify (file locations)
- C1 Flag Rule (overflow vs. underflow)
- Testing Checklist
- 8087 Compliance Notes

**Fast Access:**
- Jump to "Implementation Patterns" for copy-paste code
- Jump to "Tag Bit Extraction Cheat Sheet" in FILE_REFERENCE for quick lookups

---

### 3. **FPU_STACK_FAULT_FILE_REFERENCE.md** (Exact Line Numbers)
**Use this when:** You need exact line numbers and cross-references

**Contains:**
- Section 1: FPU_RegisterStack.v - All signals and line numbers
- Section 2: FPU_Core.v - Comprehensive signal map with 2877 lines analyzed
- Section 3: FPU_StatusWord.v - Status word assembly details
- Section 4: FPU_Exception_Handler.v - Why no modifications needed
- Section 5: Summary of modification points with line ranges
- Section 6: Tag bit extraction cheat sheet (ST(0) through ST(7))
- Section 7: Test point locations
- Section 8: Cross-reference table (task → file → line → signal → action)

**Fast Access:**
- Jump to "Key Code Sections to Modify" for implementation locations
- Jump to "Tag Bit Extraction Cheat Sheet" for visual reference
- Jump to "Cross-Reference" table for task-based lookup

---

## How to Use These Documents

### Scenario 1: "I need to understand the whole system"
1. Start with FPU_STACK_FAULT_IMPLEMENTATION.md
2. Read sections in order: RegisterStack → Core → Exception Handler → StatusWord
3. Review implementation points section
4. Check test cases section

### Scenario 2: "I need to add the code"
1. Open FPU_STACK_FAULT_QUICK_REFERENCE.md
2. Jump to "Implementation Patterns"
3. Copy the pattern for your use case
4. Use FILE_REFERENCE.md for exact line numbers
5. Modify FPU_Core.v accordingly

### Scenario 3: "I need to find a specific signal"
1. Use FPU_STACK_FAULT_FILE_REFERENCE.md
2. Jump to "Cross-Reference" table
3. Find your task in the "Task" column
4. Follow to file, lines, signal, and action

### Scenario 4: "I'm at a specific line and need context"
1. Use FPU_STACK_FAULT_FILE_REFERENCE.md
2. Find the section for your file (RegisterStack, Core, StatusWord, etc.)
3. Look up the line number in the tables

---

## Quick Facts

### The Three Critical Signals

1. **tag_word** (FPU_Core.v line 177)
   - 16-bit register containing tags for all 8 registers
   - Each register gets 2 bits: [11]=empty, [10]=special, [01]=zero, [00]=valid
   - Extract: `tag_word[(i*2)+1:(i*2)]` for ST(i)

2. **status_stack_fault** (FPU_Core.v line 252)
   - Single bit flag set when overflow or underflow detected
   - SET at line 2855: `status_stack_fault <= stack_overflow | stack_underflow`
   - Appears in status word bit [6]

3. **status_c1** (FPU_Core.v line 248)
   - Condition code C1 distinguishes overflow (1) vs. underflow (0)
   - Appears in status word bit [9]
   - Set during pre-operation checks

### The Four Modification Points

1. **Lines ~2670-2690**: Load operations (pre-push overflow)
2. **Lines ~1278-1500**: Binary operations (pre-op empty check)
3. **Lines ~2800-2820**: Pop operations (pre-pop underflow)
4. **Lines ~1600-1800**: Unary operations (ST(0) empty check)

### The Implementation Pattern

```verilog
// For any operation requiring checking:
wire [1:0] tag_st0 = tag_word[1:0];
wire [1:0] tag_sti = tag_word[(i*2)+1:(i*2)];

if ((tag_st0 == 2'b11) || (tag_sti == 2'b11)) begin
    status_stack_fault <= 1'b1;  // Set SF
    status_c1 <= 1'b0;             // C1=0 for underflow
    status_invalid <= 1'b1;        // Set IE
    error <= !mask_invalid;        // Error if unmasked
    temp_result <= 80'h7FFF_C000_0000_0000_0000;  // QNaN
    state <= STATE_WRITEBACK;      // Return to done
end
```

---

## File Organization

```
/home/user/MyPC2/
├── docs/
│   ├── FPU_STACK_FAULT_INDEX.md (this file)
│   ├── FPU_STACK_FAULT_IMPLEMENTATION.md (detailed analysis)
│   ├── FPU_STACK_FAULT_QUICK_REFERENCE.md (developer guide)
│   ├── FPU_STACK_FAULT_FILE_REFERENCE.md (line numbers)
│   └── (other FPU documentation)
│
└── Quartus/rtl/FPU8087/
    ├── FPU_Core.v (MODIFY THIS - 2877 lines)
    ├── FPU_RegisterStack.v (READ ONLY - 223 lines)
    ├── FPU_StatusWord.v (READ ONLY - 155 lines)
    ├── FPU_Exception_Handler.v (READ ONLY - 204 lines)
    └── (other FPU modules)
```

---

## Implementation Checklist

- [ ] Read FPU_STACK_FAULT_IMPLEMENTATION.md sections 1-4 for background
- [ ] Identify modification points using FILE_REFERENCE.md
- [ ] Copy implementation patterns from QUICK_REFERENCE.md
- [ ] Modify FPU_Core.v at 4 locations
- [ ] Add helper function: `get_tag()` for extracting tag bits
- [ ] Write testbenches for 4 test cases
- [ ] Verify SF bit appears in status word
- [ ] Verify C1 flag is set correctly (1=overflow, 0=underflow)
- [ ] Run existing test suite to verify no regressions
- [ ] Document any additional edge cases found

---

## Key Concepts

### Tag Word Format
Each register has a 2-bit tag in the tag_word:
- `00` = Valid (non-zero)
- `01` = Zero
- `10` = Special (NaN, Infinity, Denormal)
- `11` = Empty

### Tag Word Layout
```
tag_word[15:14] = ST(7) tag
tag_word[13:12] = ST(6) tag
tag_word[11:10] = ST(5) tag
tag_word[9:8]   = ST(4) tag
tag_word[7:6]   = ST(3) tag
tag_word[5:4]   = ST(2) tag
tag_word[3:2]   = ST(1) tag
tag_word[1:0]   = ST(0) tag
```

### C1 Flag Distinction
- SF=1, C1=1 means **Stack Overflow** (all 8 registers full)
- SF=1, C1=0 means **Stack Underflow** (insufficient operands)
- SF=0 means No stack fault

### When to Set SF
1. **Before PUSH**: Check if destination will be full (ST(7) non-empty)
2. **Before binary operation**: Check if both operands exist (ST(0) and ST(i))
3. **Before POP**: Check if source exists (ST(0) non-empty)
4. **Before unary operation**: Check if ST(0) exists

---

## Status Word Bit Layout (for Reference)

```
[15]    Busy (B)
[14]    Condition Code C3
[13:11] Stack Top Pointer
[10]    Condition Code C2
[9]     Condition Code C1    ← We set this
[8]     Condition Code C0
[7]     Exception Summary    ← Does NOT include SF!
[6]     Stack Fault (SF)     ← Automatic from status_stack_fault
[5]     Precision (PE)
[4]     Underflow (UE)
[3]     Overflow (OE)
[2]     Zero Divide (ZE)
[1]     Denormalized (DE)
[0]     Invalid Operation (IE)
```

---

## References

### External Standards
- Intel 8087 FPU Architecture Manual
- IEEE 754 Floating Point Standard
- MyPC2 Project CLAUDE.md

### Related Documentation
- CPU_ARCHITECTURE_BOTTLENECK_ANALYSIS.md
- HARVARD_CACHE_ARCHITECTURE.md
- FPU_*.md (other FPU documentation)

---

## Questions?

Refer to:
1. **"What is tag_word?"** → IMPLEMENTATION.md Section 1
2. **"Where is status_stack_fault?"** → FILE_REFERENCE.md Section 2
3. **"How do I extract tag bits?"** → QUICK_REFERENCE.md + FILE_REFERENCE.md Cheat Sheet
4. **"What code do I add?"** → QUICK_REFERENCE.md Implementation Patterns
5. **"What's the exact line number?"** → FILE_REFERENCE.md Cross-Reference table

---

Document Version: 1.0  
Created: 2025-11-20  
Last Updated: 2025-11-20
