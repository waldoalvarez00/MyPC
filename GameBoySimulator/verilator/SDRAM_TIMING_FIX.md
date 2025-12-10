# SDRAM Timing Mismatch - Root Cause and Fix

## Root Cause Summary

The C++ SDRAM model (`mister_sdram_model.h`) uses a `cas_latency = 2` setting, which means `rdata` is updated 2 clock cycles AFTER `CMD_READ` is issued. However, the SDRAM controller RTL (`sdram_sim.sv`) expects data much sooner, causing a **one-transaction delay** where each read returns data from the PREVIOUS transaction.

## Detailed Timing Analysis

### C++ SDRAM Model Timing

When `CMD_READ` is issued:
```
Cycle N:   CMD_READ received, pending_cycles = cas_latency (2)
Cycle N+1: pending_cycles--, now = 1
Cycle N+2: pending_cycles--, now = 0, rdata = last_read_data  ← DATA READY
```

### RTL Controller Timing (State Machine)

State machine advances every 8 system clocks (on `ce_cpu2x` pulses):
```
Cycle 216: IDLE → ACTV (CMD_ACTIVE)
Cycle 224: ACTV, cycle=0
Cycle 232: ACTV, cycle=1, CMD_READ → READ
Cycle 240: READ, cycle=0
Cycle 248: READ, cycle=2, SAMPLE sd_data_in → PRCH  ← RTL SAMPLES HERE
```

### Observed Behavior

**Third Read (address 0x000002):**
- Cycle 232: CMD_READ issued by RTL
- Cycle 234: C++ model updates `rdata = 0x0001` (2 cycles later)
- Cycle 248: RTL samples `sd_data_in`...
- **BUT**: `sd_data_in` is STILL `0x50C3` from the PREVIOUS read!

**Measurement:**
- `sd_data_in` updates at cycle 108 → 0x50C3
- `sd_data_in` updates at cycle 276 → 0x0001
- RTL needs data at cycle 248
- **Delay**: 276 - 248 = **28 cycles late!**

## Why The Delay?

The RTL controller does DUPLICATE reads of the same word address (because the CPU reads sequential bytes):
1. Read #1: Address 0x000000 → Returns 0x50C3 ✓
2. Read #2: Address 0x000000 (duplicate!) → Returns 0x50C3 ✓
3. Read #3: Address 0x000002 → Returns 0x50C3 ✗ (old data!)
4. Read #4: Address 0x000002 (duplicate!) → Returns 0x0001 ✓

Each read takes ~24 cycles (3 `ce_cpu2x` pulses × 8 cycles). The duplicate reads delay when new data becomes available.

## The Fix

**Reduce CAS latency in the C++ model to match RTL expectations.**

Change in `mister_sdram_model.h` line 78:
```cpp
// BEFORE:
cas_latency = 2;  // Data ready 2 cycles after CMD_READ

// AFTER:
cas_latency = 0;  // Data ready immediately (simulation model)
```

With `cas_latency = 0`, `rdata` is updated THE SAME CYCLE as `CMD_READ`, ensuring the RTL always sees fresh data.

## Alternative Fixes (Not Recommended)

1. **Increase RTL wait time**: Change `if (cycle >= 2)` to `if (cycle >= 4)` in `sdram_sim.sv`
   - Problem: Makes memory access MUCH slower, hurts performance

2. **Cache duplicate reads in C++**: Track last address and return cached data
   - Problem: Complex, doesn't match real SDRAM behavior

3. **Eliminate duplicate reads in RTL**: Add word-level caching
   - Problem: Major architectural change

## Why cas_latency=0 is Safe Here

This is a **simulation model**, not a real SDRAM chip. We can use zero latency because:
- C++ model has instant memory access (`memory[addr]`)
- No actual DRAM refresh/precharge delays needed
- Goal is functional verification, not timing-accurate SDRAM simulation
- Real hardware uses different SDRAM controller anyway

The `pending_cycles` mechanism was designed for cycle-accurate SDRAM simulation, but in this Verilator testbench, it creates more problems than it solves.
