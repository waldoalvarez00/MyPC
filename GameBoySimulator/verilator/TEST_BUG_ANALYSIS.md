# Test Bug Analysis Report
## Date: 2025-12-11

## Summary of Test Fixes

I've fixed several test bugs and uncovered a **critical CPU core issue**:

### ✅ Fixed Tests

#### 1. test_lcd_output.cpp - FIXED (Boot ROM upload missing)
**Problem**: Test never uploaded boot ROM, so CPU had nothing to execute
**Fix Applied**: Added boot ROM creation and upload sequence (lines 34-75)
**Result**: Boot ROM now completes successfully ✅
**Remaining Issue**: LCD still doesn't turn on (real game needs more initialization time)

#### 2. test_jr_instruction.cpp - CREATED (New diagnostic test)
**Purpose**: Isolate JR instruction issue
**Result**: Confirmed JR instruction DOES NOT execute ❌

### ❌ Critical Bug Discovered: JR Instruction Fails

## JR vs JP Diagnostic Results

```
Test Configuration:
  0x0150: JP $0160 (3-byte instruction)
  0x0160: JR +2 → $0163 (2-byte instruction)

Execution Trace:
  PC[ 5]: $0150 (opcode=0xC3)  ← JP opcode
  PC[ 6]: $0151 (opcode=0x60)  ← JP low byte
  PC[ 7]: $0152 (opcode=0x01)  ← JP high byte
  PC[ 8]: $0160 (opcode=0x18)  ← ✅ JP worked! Now at JR

  PC[ 8]: $0160 (opcode=0x18)  ← JR opcode
  PC[ 9]: $0161 (opcode=0x02)  ← JR offset
  PC[10]: $0162 (opcode=0x76)  ← ❌ HALT! JR didn't jump!

Results:
  JP (3-byte): ✅ WORKS
  JR (2-byte): ❌ FAILS
```

## Root Cause Analysis

### What We Know
1. ✅ TV80 core is correctly configured with Mode=3 (GameBoy/LR35902)
2. ✅ SDRAM wait state logic is working (JP executes correctly)
3. ✅ Multi-byte instruction fetch works (JP fetches 3 bytes correctly)
4. ❌ JR instruction fetches both bytes but doesn't execute the jump

### Evidence

From [`tv80_gameboy.v:60`](gb:tv80_gameboy.v:60):
```verilog
tv80_core #(
    .Mode(3),           // GameBoy mode (LR35902)
    .IOWait(IOWait)
) i_tv80_core (
```

### JR Instruction Specification

According to [GameBoy opcodes](https://www.pastraiser.com/cpu/gameboy/gameboy_opcodes.html):
- **Opcode**: 0x18 (JR e)
- **Length**: 2 bytes
- **Cycles**: 12 cycles
- **Operation**: PC = PC + e (signed 8-bit offset)
- **Offset calculation**: PC after fetching instruction + signed offset

### Hypothesis 1: TV80 Core Bug in GameBoy Mode
**Evidence**:
- JP works (opcode 0xC3)
- JR doesn't work (opcode 0x18)
- Both are multi-byte instructions
- TV80 claims to support GameBoy mode and pass Blargg's tests

**Counter-evidence**:
- User's GUI shows game executing with jumps working
- Original MiSTer core works with same TV80

### Hypothesis 2: Wait State Timing Issue
**Evidence**:
- JR is 2-byte (opcode + offset)
- JP is 3-byte (opcode + addr_lo + addr_hi)
- Different byte counts might have different timing requirements

**Analysis of wait state logic** (`gb.v:308-336`):
```verilog
wire cpu_reading_ext_bus = (sel_ext_bus & ~cpu_rd_n & ~cpu_mreq_n);

always @(posedge clk_sys) begin
    if (reset) begin
        sdram_wait_counter <= 2'd0;
        sdram_wait_active <= 1'b0;
    end else if (ce) begin  // Using 'ce' not 'ce_cpu'
        if (cpu_reading_ext_bus && !sdram_wait_active) begin
            sdram_wait_counter <= 2'd2;  // 2 cycles for CAS latency
            sdram_wait_active <= 1'b1;
        end else if (sdram_wait_active) begin
            if (sdram_wait_counter > 0) begin
                sdram_wait_counter <= sdram_wait_counter - 2'd1;
            end else begin
                sdram_wait_active <= 1'b0;
            end
        end
    end
end

wire sdram_ready = ~sdram_wait_active;
wire cpu_clken = ~hdma_cpu_stop & ce_cpu & sdram_ready;
```

**Issue**: Wait state triggers on `cpu_reading_ext_bus && !sdram_wait_active`. This means:
1. First fetch → triggers wait (counter=2)
2. After 2 'ce' cycles → wait completes (counter=0, wait_active=0)
3. Second fetch → should trigger new wait
4. **But**: If CPU hasn't deasserted read signals between fetches, `cpu_reading_ext_bus` stays high continuously

### Hypothesis 3: CPU Signal Timing
**Possible issue**: `cpu_rd_n` and `cpu_mreq_n` might remain asserted during multi-byte instruction fetch, causing wait state logic to only trigger once for the entire instruction instead of once per byte.

## User's Game Works - Why?

The user reported game working in GUI with successful jumps:
```
Cart PC[  19]: $DFFF  ← Jump to RAM
Cart PC[  50]: $C1B5  ← Jump to function
Cart PC[  56]: $34D1  ← ROM bank switching
```

**Possible explanations**:
1. Game uses JP/CALL/RET instead of JR
2. JR works in different timing conditions (different SDRAM state)
3. Test has additional issue not present in real game

## Recommended Actions

### Immediate
1. ✅ Fixed test_lcd_output boot ROM upload
2. ✅ Created test_jr_instruction for diagnosis
3. **TODO**: Check if real game uses JR instruction

### Investigation Needed
1. **Verify JR usage**: Check if TOBU game ROM contains JR instructions
2. **Cycle-accurate trace**: Add debug output showing:
   - cpu_rd_n / cpu_mreq_n state each cycle
   - sdram_wait_active state
   - When wait states trigger
3. **Compare with original**: Test same ROM on original MiSTer GameBoy core

### Potential Fixes
1. **If JR not used in games**: Document as known limitation, not critical
2. **If wait state issue**: Modify logic to trigger on each byte fetch
3. **If TV80 bug**: May need TV80 core patch or different CPU core

## Test Files Modified

1. **test_lcd_output.cpp**:
   - Added boot ROM creation (lines 34-50)
   - Added boot ROM upload (lines 61-75)
   - Result: Boot ROM completes, LCD initialization pending

2. **test_jr_instruction.cpp** (NEW):
   - Tests both forward (+3) and backward (-3) JR
   - Confirms JR instruction failure
   - Shows PC incrementing byte-by-byte instead of jumping

3. **test_jr_diagnostic.cpp** (NEW):
   - Side-by-side comparison of JP vs JR
   - Confirms JP works, JR fails
   - Narrows down to 2-byte vs 3-byte instruction issue

## Sources

- [GameBoy opcodes reference](https://www.pastraiser.com/cpu/gameboy/gameboy_opcodes.html)
- [TV80 core on OpenCores](https://opencores.org/projects/tv80)
- [T80/TV80 GameBoy mode support](https://github.com/EisernSchild/t80)
- [GameBoy CPU instruction set](https://gbdev.io/gb-opcodes/)

## Next Steps for User

1. **Rebuild GUI simulator** in Visual Studio (primary goal)
2. **Test real game** - see if it works despite JR issue
3. **Report back**: Does game work? Any stuck PC?
4. **If game works**: JR issue may be test artifact
5. **If game fails**: We need to fix JR instruction execution

## Status

- ✅ test_lcd_output: Boot ROM upload fixed
- ❌ test_lcd_output: LCD initialization (needs more investigation)
- ❌ test_jr_instruction: JR instruction doesn't execute (TV80/wait state issue)
- ✅ test_jp_instruction: Still passing (JP works correctly)
- ⏳ User testing: Awaiting Visual Studio rebuild and game test

**Priority**: User should test GUI simulator first to determine if JR issue affects real gameplay.
