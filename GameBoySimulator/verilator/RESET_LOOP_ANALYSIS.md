# Reset Loop Analysis

## Problem Found

The trace shows the real DMG boot ROM IS executing, but then gets stuck in a reset loop:

```
Boot PC[   1]: $0000
Boot PC[   2]: $0001
...
Boot PC[   6]: $0005  ← Real DMG ROM logo scroll subroutine!
...
Boot PC[ 200]: $0009
... (boot trace truncated)
LCD state changed: lcd_on=1 [ON] (change #1)
*** PC at $0000 (boot ROM start)  ← Repeated hundreds of times!
*** PC at $0000 (boot ROM start)
*** PC at $0000 (boot ROM start)
...
Total boot ROM instructions executed: 65,983
```

## What's Happening

1. ✅ Real DMG boot ROM loads successfully
2. ✅ CPU starts executing at $0000  
3. ✅ Logo copying loop runs ($0006 → $8000-$801F tile data copy)
4. ❌ CPU keeps returning to $0000 (reset/restart)
5. ❌ Never progresses past logo copy to show animation

## Execution Pattern Analysis

Normal boot ROM loop (seen in trace):
- $0006: LD A, (DE)    - Load tile byte
- $8000: [memory access to VRAM]
- $0007: LD (HL+), A   - Store to VRAM
- $0008: INC DE        - Next source byte
- $0009: DEC C         - Decrement counter
- $000A: JR NZ, $0006  - Loop if not done
- $000B: (next instruction)

This loop should run 48 times (copy 48 bytes of logo tile data), then continue.

## IMPORTANT NOTE

From CPU_ADDRESS_EXPLANATION.md:
> **dbg_cpu_addr is the ADDRESS BUS, not the Program Counter (PC)!**

So "PC at $0000" actually means "CPU accessing address $0000" which could be:
1. Fetching instruction at $0000 (normal after reset/interrupt)
2. Reading data from $0000
3. Address bus stuck at $0000 due to CPU halt

## Possible Root Causes

### 1. Interrupt Triggering
- VBlank/LCD interrupts might be enabled too early
- Interrupt jumps CPU to $0040 (VBlank vector) or $0048 (LCD STAT vector)
- If interrupt handler not initialized, could crash and reset

### 2. CPU Clock Enable (ce_cpu) Issue
- From sim log: "Clock divider started, ce_cpu=0"
- If ce_cpu glitches or stops, CPU might halt mid-instruction
- Address bus would show last fetch address

### 3. HDMA or DMA Interference
- From gb.v line 307: `wire cpu_clken = ~hdma_cpu_stop & ce_cpu;`
- If hdma_cpu_stop asserts incorrectly, CPU stops
- This is DMG mode, HDMA shouldn't even be active

### 4. Reset Signal Glitch
- From gb.v line 349: `.RESET_n ( !reset_ss )`
- If reset_ss pulses repeatedly, CPU would restart at $0000
- Need to check reset_ss state during boot

## Next Steps to Debug

1. **Add interrupt status logging:**
   - Log `dbg_ie` (Interrupt Enable)
   - Log `dbg_if` (Interrupt Flags)  
   - Log `dbg_ime` (Interrupt Master Enable)
   - See if VBlank interrupt is firing too early

2. **Add clock enable monitoring:**
   - Track `dbg_ce_cpu` / `dbg_cpu_clken`
   - See if clock stops during boot

3. **Add reset monitoring:**
   - Track reset_ss signal
   - See if CPU is being reset repeatedly

4. **Check instruction fetch vs data access:**
   - Log `dbg_cpu_rd_n` (read signal)
   - Log `dbg_cpu_mreq_n` (memory request)
   - Determine if $0000 accesses are instruction fetches or data reads

## Expected Behavior

Real DMG boot ROM should:
1. Copy Nintendo logo tiles to VRAM ($0000-$0034)
2. Scroll logo down ($0035-$00D4)  
3. Play "ding" sound and timing delays ($00D5-$00F7)
4. Check cart header checksum ($00F8-$00FB)
5. Disable boot ROM at $00FC (write to $FF50)
6. Jump to cart entry point $0100

Currently stuck at step 1 (tile copying loop).
