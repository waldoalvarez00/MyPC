# CPU Implementation Comparison Analysis

## Problem Summary

After fixing SDRAM data path issues, we discovered two critical bugs in the GameBoy CPU execution:

1. **cart_rd goes low (inactive) after JP instruction** - CPU doesn't request new instruction fetch
2. **CPU jumps to wrong address** - Jumps to 0x01C3 instead of 0x0150

## CPU Implementation Details

The GameBoy simulator uses **TV80 (Verilog Z80)** wrapped by `tv80_gameboy.v`, NOT the VHDL T80/GBse.

### File: `/rtl/tv80_gameboy.v`

This Verilog module provides a drop-in replacement for the VHDL GBse module:

```verilog
module GBse #(parameter T2Write = 2, IOWait = 1) (
    // Same interface as VHDL GBse
    output reg RD_n,   // Read strobe (active low)
    output reg WR_n,   // Write strobe (active low)
    output reg MREQ_n, // Memory request (active low)
    output reg IORQ_n, // I/O request (active low)
    ...
);
```

### RD_n Generation Logic (lines 98-126)

```verilog
else if (CLKEN) begin
    // Default: all inactive
    RD_n   <= 1'b1;
    WR_n   <= 1'b1;
    IORQ_n <= 1'b1;
    MREQ_n <= 1'b1;

    // ... (M1 cycle handling)

    else begin
        // Memory/IO read
        if ((tstate[1] || tstate[2]) && no_read == 1'b0 && write == 1'b0) begin
            RD_n   <= 1'b0;  // ACTIVE during T1 or T2
            IORQ_n <= ~iorq;
            MREQ_n <= iorq;
        end
    end
```

**Key Point:** RD_n is only active when:
- tstate[1] OR tstate[2] (T-states 1 or 2)
- no_read == 0 (CPU wants to read)
- write == 0 (not a write cycle)

## Observed Behavior

From `test_simple_lcd.cpp` output at cycle 468:

```
468 | 0x01C3 | 0x00   | 0x0001   | rd=0 oe=0 st=1 addr=0x000E1 |
```

After jumping from PC 0x0004:
- PC changed to 0x01C3 (wrong address)
- cart_rd = 0 (CPU not requesting read)
- sdram_oe = 0 (SDRAM output disabled)
- sdram_addr = 0x000E1 (corresponds to PC 0x01C3)

## Jump Address Bug Analysis

ROM layout (byte addresses):
```
0x0000: C3       (JP opcode)
0x0001: 50       (low byte of target address)
0x0002: 01       (high byte of target address)
Target should be: (0x01 << 8) | 0x50 = 0x0150
```

CPU actually jumped to: **0x01C3**

Breaking down 0x01C3:
- High byte: 0x01 ✓ (correct)
- Low byte: 0xC3 (this is the OPCODE byte!)

**Hypothesis:** The CPU used the opcode byte (0xC3) as the low byte of the jump target.

## cart_rd Signal Path

```
cart_rd = cart_sel & ext_bus_rd                    (gb.v:1033)
ext_bus_rd = ... | (sel_ext_bus & ~cpu_rd_n)       (gb.v:1022)
cpu_rd_n comes from GBse/tv80_gameboy.v RD_n output
```

When cart_rd=0, the SDRAM controller never activates because sdram_oe=0:
```verilog
assign sdram_oe = ~cart_download & cart_rd & ~cram_rd;  (gameboy_sim.v:132)
```

## Next Steps

1. **Investigate TV80 core** (`tv80_core.v`, `tv80_mcode.v`) to understand:
   - Why `no_read` / `write` signals are incorrect after JP
   - Why the JP instruction is decoding bytes in the wrong order

2. **Compare with working VHDL T80** to see if this is a TV80 Verilog port bug

3. **Check GameBoy mode (Mode 3)** implementation in TV80 - the LR35902 CPU has specific quirks

4. **Test with VHDL GBse** instead of Verilog wrapper to see if issue persists

## Files to Investigate

- `/tv80/rtl/core/tv80_core.v` - Main CPU state machine
- `/tv80/rtl/core/tv80_mcode.v` - Microcode/instruction decode (101KB!)
- `/gameboy_core/rtl/T80/T80.vhd` - Original VHDL implementation
- `/gameboy_core/rtl/T80/T80_MCode.vhd` - VHDL microcode

## Status

- ✓ SDRAM data path fixed (persistent rdata, correct addressing)
- ✓ cart_ready signal working
- ✗ CPU RD_n timing after JP (TV80 core issue)
- ✗ JP instruction operand byte order (TV80 Mode 3 bug?)
