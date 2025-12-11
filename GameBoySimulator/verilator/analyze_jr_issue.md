# Conditional JR Analysis

## The Problem

My fix subtracts 1 from all JumpE offsets:
```verilog
if (JumpE == 1'b1 )
  PC16_B = { {8{DI_Reg[7]}}, DI_Reg } - 1;
```

But this breaks conditional JR when the condition is FALSE!

## Conditional JR Microcode Behavior

From tv80_mcode.v lines 1333-1338:

```verilog
case (IR[4:3])
  3 : MCycles = (F[Flag_C]) ? 3'd2 : 3'd3;   // JR C
endcase
```

For JR C (0x38):
- If Carry SET (TRUE): MCycles = 2 (M1, M2 only)
- If Carry CLEAR (FALSE): MCycles = 3 (M1, M2, M3 with JumpE=1)

## The Bug This Creates

Test case: JR C when carry is CLEAR (should NOT jump)
- MCycles = 3 (because condition FALSE)
- M3 executes with `JumpE = 1`
- My fix subtracts 1 from offset
- **Result: It JUMPS when it shouldn't!**

Observed behavior:
- PC: $0151 → $0152 → $0153 → $0157
- Should be: $0151 → $0152 → $0153 → $0154 → $0155 (no jump)
- Actually jumped by offset (+5 - 1 = +4 from $0153)

## Why This Happens

The TV80 conditional JR logic seems backwards:
- Condition TRUE → MCycles = 2 → No M3 → How does it jump?
- Condition FALSE → MCycles = 3 → M3 with JumpE → Shouldn't jump!

## Possible Explanations

1. **TV80 Bug**: The microcode logic is wrong
2. **Missing Logic**: There's additional logic that disables JumpE when condition is FALSE
3. **Different Mechanism**: When MCycles = 2, the jump happens via a different mechanism
4. **My Fix is Wrong**: The -1 compensation should only apply to specific cases

## Solution Options

### Option 1: Only fix unconditional JR (0x18)
Check IR value and only apply -1 for opcode 0x18

### Option 2: Check if in M2 vs M3
Different compensation for 2-cycle vs 3-cycle instructions

### Option 3: Investigate original TV80 behavior
Test TV80 without my fix to see if conditional JR worked originally

### Option 4: Different fix approach
Maybe the issue isn't with JumpE offset but with when PC increments
