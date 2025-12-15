# FPU8087 Invalid Operation (IE) Exception - Quick Reference

## Status Word Bits (16-bit format)
```
[15]    B    Busy flag
[14]    C3   Condition code
[13:11] TOP  Stack pointer (0-7)
[10]    C2   Condition code
[9]     C1   Condition code (SF indicator)
[8]     C0   Condition code
[7]     ES   Exception Summary (auto-set)
[6]     SF   Stack Fault (OV | UF)
[5]     PE   Precision exception
[4]     UE   Underflow exception
[3]     OE   Overflow exception
[2]     ZE   Zero Divide exception
[1]     DE   Denormal exception
[0]     IE   Invalid Operation exception ← TARGET
```

## Control Word Bits (16-bit format)
```
[11:10] RC   Rounding control (00=nearest, 01=down, 10=up, 11=truncate)
[9:8]   PC   Precision (00=24b, 10=53b, 11=64b extended)
[5]     PM   Mask precision exception (1=masked)
[4]     UM   Mask underflow (1=masked)
[3]     OM   Mask overflow (1=masked)
[2]     ZM   Mask zero divide (1=masked)
[1]     DM   Mask denormal (1=masked)
[0]     IM   Mask invalid operation (1=masked) ← CONTROL FOR IE
```

## IE Exception Triggers
1. **SNaN operand** - Signaling NaN in any operation
2. **Stack empty** - Operating on ST(i) with tag=11
3. **Inf+(-Inf)** - Invalid infinity operations
4. **0×Inf** - Invalid multiplication
5. **0/0, Inf/Inf** - Invalid division
6. **sqrt(negative)** - Invalid square root

## Tag Word (2 bits × 8 registers)
```
00 = Valid (non-zero)
01 = Zero
10 = Special (NaN, Inf, Denormal)
11 = Empty ← Triggers stack empty IE
```

## Exception Signal Flow
```
ArithmeticUnit.flag_invalid (1 cycle)
  ↓
FPU_Exception_Handler.exception_latch (control signal)
  ↓
exception_invalid_latched (sticky)
  ↓
Check: exception_invalid && !mask_invalid
  ↓
int_request ← 1 (if unmasked)
status_word[0] ← 1
status_word[7] ← 1 (ES auto-set)
```

## Key Control Signals
```
execute          (input)   - Pulse to start FPU operation
ready            (output)  - FPU ready for next instruction
int_request      (output)  - Active HIGH when unmasked exception
status_out[15:0] (output)  - Status word
control_in[15:0] (input)   - Control word
tag_word_out     (output)  - Register tags [1:0] per register
```

## FPU_Core Instructions
```
FINIT  = 8'hF0  Initialize (clear stack, reset SP=0)
FLD    = 8'h20  Push onto stack
FLDCW  = 8'hF1  Load control word
FSTCW  = 8'hF2  Store control word
FSTSW  = 8'hF3  Store status word
FCLEX  = 8'hF4  Clear exceptions
FADD   = 8'h10  Add
FSUB   = 8'h12  Subtract
FMUL   = 8'h14  Multiply
FDIV   = 8'h16  Divide
```

## Default Values
```
Control word: 0x037F (all exceptions masked, round nearest, extended precision)
To unmask IE: 0x027F (bit 0 = 0)
```

## FP80 Constants (80-bit extended precision)
```
Zero:      80'h0000_0000000000000000
One:       80'h3FFF_8000000000000000
Two:       80'h4000_8000000000000000
Negative 1: 80'hBFFF_8000000000000000
```

## Testbench Pattern
```
1. Initialize: reset = 1, wait 20 clks, reset = 0
2. Execute: instruction + data_in, pulse execute
3. Wait: for ready signal (timeout after 500 clks)
4. Check: status_out[0] = IE, int_request state
5. Report: PASS if expected behavior matches
```

## Files Quick Reference
| File | Purpose | Lines |
|------|---------|-------|
| FPU_Exception_Handler.v | Exception latching & INT | 204 |
| FPU_StatusWord.v | Status word construction | 154 |
| FPU_RegisterStack.v | Stack & tag management | 222 |
| FPU_Core.v | FPU integration | 1000+ |
| FPU_ControlWord.v | Control word decode | 91 |
| fpu_core_tb.sv | Example testbench | 466 |
| run_fpu_core_test.sh | Test execution script | 85 |

