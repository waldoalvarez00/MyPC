# SDRAM Controller Latency Bug Analysis

## Problem Summary

The SDRAM controller exhibits a **one-transaction delay** - it returns data from the PREVIOUS read instead of the current one.

Test output shows:
- **Third read** (address 0x00000001): Returns 0x50C3 (data from first read at address 0x00000000) ✗
- **Fourth read** (address 0x00000001): Returns 0x0001 (correct data for address 0x00000001) ✓

## Root Cause: Timing Mismatch

### SDRAM Controller RTL Timing (sdram_sim.sv)

State machine advances on `ce_cpu2x` pulses (every 8 system clocks):

1. **IDLE** (cycle 216): See `oe_pending=1`, issue `CMD_ACTIVE`, → ACTIVATE
2. **ACTIVATE** (cycle 224-232): Wait `cycle >= 1`, issue `CMD_READ`, → READ
3. **READ** (cycle 232-248): Wait `cycle >= 2`, **SAMPLE `sd_data_in`**, → PRECHARGE

**Total delay**: 3 sync pulses (24 system clocks) from request to sampling

### C++ SDRAM Model Timing (mister_sdram_model.h)

```cpp
// Line 130-136: Pending cycles countdown
if (pending_cycles > 0) {
    pending_cycles--;
    if (pending_cycles == 0 && current_state == 1) {
        rdata = last_read_data;  // Update rdata HERE
    }
}

// Line 166-187: Process CMD_READ
case CMD_READ:
    last_read_data = memory[byte_addr];  // Read from memory
    pending_cycles = cas_latency;  // Set to 2
    break;
```

When `CMD_READ` is issued:
1. **Call N** (cycle 232): Process `CMD_READ`
   - `last_read_data = memory[1] = 0x0001` (read NEW data from memory)
   - `pending_cycles = 2`
   - `rdata` UNCHANGED (still 0x50C3 from previous read!)

2. **Call N+1** (cycle 233): `pending_cycles` decrements 2 → 1
3. **Call N+2** (cycle 234): `pending_cycles` decrements 1 → 0, **`rdata = 0x0001`**

**Problem**: RTL samples `sd_data_in` at cycle 248, which is connected to `sdram_rdata`.
But `processSDRAM()` is called EVERY clock cycle, so by cycle 234, `rdata` should be 0x0001.

## Why Data Appears One Transaction Late

Looking at the trace sequence:

### First Read (address 0x00000000):
- Cycle 26: CMD_READ issued
- Cycle ~28-29: `last_read_data = 0x50C3`, `pending_cycles = 2`
- Cycle ~30-31: `rdata = 0x50C3` ✓
- Cycle 74: RTL samples 0x50C3 ✓

### Second Read (address 0x00000000 - duplicate):
- Same process, returns 0x50C3 again ✓

### Third Read (address 0x00000001):
- Cycle 232: CMD_READ issued (ce_cpu2x pulse, every 8 cycles)
- C++ model: `last_read_data = 0x0001`, `pending_cycles = 2`
- Cycle 234: `rdata = 0x0001` should happen here!
- Cycle 248: RTL samples... **but sees 0x50C3!** ✗

### Fourth Read (address 0x00000001):
- Cycle 362: CMD_READ issued
- C++ model: `last_read_data = 0x0001`, `pending_cycles = 2`
- Cycle 408: RTL samples 0x0001 ✓

## The Actual Bug

The issue is that **`processSDRAM()` is only called when a command is issued**!

Looking at the RTL's command generation (sdram_sim.sv lines 137-140):

```verilog
// CRITICAL: Default cmd to NOP on EVERY clock cycle
cmd <= CMD_NOP;
```

BUT - the RTL sets `cmd <= CMD_NOP` on **every** clock cycle, not just when `ce_cpu2x` is active!

The C++ model is called like this in test_simple_lcd.cpp:

```cpp
void tick() {
    clk = !clk;
    top->clk_sys = clk;
    top->eval();
    if (clk) {
        processSDRAM();  // Called EVERY posedge
    }
}
```

So `processSDRAM()` sees:
- Cycle 232 (ce_cpu2x=1): CMD_READ
- Cycle 233-239 (ce_cpu2x=0): CMD_NOP (7 calls)
- Cycle 240 (ce_cpu2x=1): CMD_NOP
- Cycle 241-247 (ce_cpu2x=0): CMD_NOP (7 calls)
- Cycle 248 (ce_cpu2x=1): CMD_NOP

During all those CMD_NOP calls, `pending_cycles` should be decrementing!

Let me verify the decrement logic:

```cpp
// Line 130: Check if pending_cycles > 0
if (pending_cycles > 0) {
    pending_cycles--;  // Decrements EVERY call!
}
```

So:
- Cycle 232: CMD_READ, pending_cycles = 2
- Cycle 233: CMD_NOP, pending_cycles = 1 (decrement)
- Cycle 234: CMD_NOP, pending_cycles = 0 (decrement), rdata = 0x0001!

**This should work!** By cycle 234, rdata is updated. RTL samples at cycle 248.

## Missing Piece: `sd_data_in` Assignment

Wait - I need to check if `sdram_rdata` is actually being assigned to `top->sd_data_in`!

In test_simple_lcd.cpp:
```cpp
void processSDRAM() {
    sdram->processNativeSDRAM(
        ...,
        sdram_rdata,  // rdata is passed by reference
        ...
    );
    top->sd_data_in = sdram_rdata;  // Assign to RTL input
}
```

So every call to `processSDRAM()` updates `sdram_rdata` and assigns it to `top->sd_data_in`.

**But!** The RTL only samples `sd_data_in` at specific times (during READ state when cycle >= 2).

Let me check when exactly the RTL's `dout` register is updated...

In sdram_sim.sv line 240:
```verilog
dout <= sd_data_in;  // Sample when cycle >= 2 in READ state
```

This happens on a clock edge when `sync` is high and `state == READ` and `cycle >= 2`.

So even though `sd_data_in` is updated to 0x0001 at cycle 234, the RTL doesn't sample it until cycle 248 (the next ce_cpu2x pulse when cycle >= 2).

But by cycle 248, does `sd_data_in` still hold 0x0001?

Let me check if there's any other read happening between 234 and 248...

Looking at the trace: cart_rd goes to 0 at cycle 280, so there's no new read request until after cycle 298.

**So `sd_data_in` should hold 0x0001 from cycle 234 onwards!**

## Hypothesis: CMD_NOP Clears `rdata`

Let me check if the C++ model clears `rdata` on CMD_NOP...

Looking at mister_sdram_model.h line 127:
```cpp
// DON'T clear rdata - let it hold until next read!
// rdata = 0;  // COMMENTED OUT
```

Good, rdata is NOT cleared.

But wait - what if there's a state reset or something?

Actually, I just realized - let me check the EXACT sequence of ce_cpu2x pulses relative to when rdata updates:

- Cycle 216: ce_cpu2x pulse, IDLE → ACTV
- Cycle 224: ce_cpu2x pulse, ACTV (cycle 0)
- Cycle 232: ce_cpu2x pulse, ACTV (cycle 1), CMD_READ issued, → READ
  - processSDRAM: CMD_READ, pending_cycles = 2, last_read_data = 0x0001
- Cycle 240: ce_cpu2x pulse, READ (cycle 1)
  - processSDRAM: CMD_NOP, pending_cycles-- (from 2 to 1)
- Cycle 248: ce_cpu2x pulse, READ (cycle 2), SAMPLE sd_data_in
  - processSDRAM: CMD_NOP, pending_cycles-- (from 1 to 0), rdata = 0x0001

**AH HA!** The rdata update happens AT THE SAME TIME as the RTL samples!

On cycle 248:
1. RTL eval() runs FIRST
2. RTL samples sd_data_in (which is still 0x50C3)
3. THEN processSDRAM() is called
4. processSDRAM() updates rdata to 0x0001
5. Too late - RTL already sampled!

## The Fix

The issue is that `processSDRAM()` is called AFTER `top->eval()` in the tick() function. So the RTL sees the OLD value of `sd_data_in`.

We need to call `processSDRAM()` BEFORE `top->eval()` so that `sd_data_in` is updated before the RTL samples it.

Actually, better yet - we need to count ce_cpu2x pulses, not system clock cycles, for pending_cycles!

Or simplest fix: Call processSDRAM() BEFORE eval() on posedge.
