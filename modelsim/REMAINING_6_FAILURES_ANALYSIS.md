# Remaining 6 Failures - Detailed Analysis

## Summary
**Status**: 12 → 6 failures (50% reduction achieved)
**Root Cause**: Victim writeback address corruption
**Complexity**: Deep architectural issue requiring careful fix

## Failures Fixed ✅

### 1. SDRAM One-Cycle Latency Bug (Commit: 4db2957)
- **Impact**: 12 → 10 failures
- **Symptom**: Cache receiving stale data from previous memory access
- **Fix**: Changed `mem_data_in <= sdram[...]` to `assign mem_data_in = sdram[...]` (combinatorial)

### 2. golden_write Initialization Bug (Commit: 68b059b)
- **Impact**: 10 → 6 failures
- **Symptom**: Cache fills reading 0x0000 instead of test data
- **Fix**: Modified `golden_write()` to write to both `golden[]` and `sdram[]` arrays

## Remaining 6 Failures (ROOT CAUSE IDENTIFIED)

### Failure List
1. `FAIL[94]`: DLOAD addr=0x002fc got=0000 exp=816d
2. `FAIL[111]`: DLOAD addr=0x00394 got=0000 exp=4c3c
3. `FAIL[124]`: IFETCH addr=0x0011e got=1979 exp=0000
4. `FAIL[151]`: DLOAD addr=0x002a2 got=0000 exp=2f96
5. `FAIL[156]`: IFETCH addr=0x000de got=b52a exp=0000
6. `FAIL[182]`: DLOAD addr=0x000a4 got=0000 exp=5bf8

### Common Pattern
**ALL 6 failures involve victim writeback operations** - victim WB writes to wrong addresses, corrupting memory.

### Detailed Example: Address 0x00394

**Timeline**:
```
[19165000] ICache reads addr=0x00394 → data=0x4c3c ✓ (SDRAM correct)
[19465000] Victim=0 CAPTURED at addr=0x00720 ✓ (correct address)
[19635000] Victim=0 ENQUEUED addr=0x00720 ✓ (correct)
[19645000] Victim=0 WB STARTS
[19725000] Victim WB writes addr=0x00394 → data=0x0000 ✗ (WRONG ADDRESS!)
           ^^^ Should write to 0x00720, but writes to 0x00394!
[29805000] DCache fills addr=0x00394 → data=0x0000 ✗ (corrupted SDRAM)
```

### Root Cause: victim_addr[] Corruption

**Evidence**:
- Victim=0 captured for base address 0x0072 (from addr 0x00720)
- Victim=0 WB writes to base address 0x0039 (addr 0x00390-0x00397)
- **victim_addr[0] contains wrong value at WB time!**

### Investigation Attempts

#### Attempt 1: Fix victim_wb_beat Counter ❌
**Hypothesis**: victim_wb_addr uses `flush_beat` instead of `victim_wb_beat[victim_capture_id]`

**Fix Applied**:
```systemverilog
// Changed from:
wire [19:1] victim_wb_addr = {victim_addr[victim_capture_id], flush_beat};

// To:
wire [19:1] victim_wb_addr = {victim_addr[victim_capture_id], victim_wb_beat[victim_capture_id]};
```

**Result**: Still 6 failures! Address 0x00720 still writes to 0x00390.

**Conclusion**: The beat counter wasn't the issue - victim_addr[] itself is corrupted!

#### Attempt 2: Hybrid Approach (Both Counters) ❌
**Hypothesis**: Other code depends on flush_beat being valid

**Fix Applied**: Keep both flush_beat and victim_wb_beat synchronized

**Result**: Still 6 failures with same wrong addresses

**Conclusion**: Confirms victim_addr[] is the problem, not the beat counter

### True Root Cause: victim_addr[] Assignment Bug

**Current Assignment** (line 937-938):
```systemverilog
victim_addr[victim_alloc_ptr] <= {(way_to_replace ? tag_way1 : tag_way0),
                                  latched_address[index_end:index_start]};
```

**Suspected Issues**:
1. **Timing**: `tag_way*` or `latched_address` might have wrong values when sampled
2. **Overwriting**: victim_addr[] might be overwritten before WB completes
3. **Pointer Confusion**: `victim_alloc_ptr` vs `victim_capture_id` mismatch

### Evidence of Corruption

**Victim=0 Address History**:
- [18025000] CAPTURE addr=0x00300 → victim_addr[0] = 0x0030
- [19465000] CAPTURE addr=0x00720 → victim_addr[0] = 0x0072 (should be)
- [19645000] WB START victim=0
- [19725000] WB writes 0x00390 → victim_addr[0] = 0x0039 (?!)

**None of these match!** 0x0039 doesn't equal 0x0030 or 0x0072.

### Next Steps for Resolution

1. **Add Debug Instrumentation**:
   - Print victim_addr[] when assigned (capture time)
   - Print victim_addr[] when read (WB start time)
   - Track any writes to victim_addr[] between capture and WB

2. **Check Victim Buffer Lifecycle**:
   - Verify victim_alloc_ptr vs victim_capture_id usage
   - Ensure victim_addr[] isn't overwritten by new captures
   - Check if victim=0 and victim=1 buffers interfere

3. **Validate Tag/Index Sampling**:
   - Verify `tag_way*` and `latched_address` are stable when captured
   - Check for timing hazards in the capture logic
   - Ensure no combinatorial loops

4. **Test Hypothesis**:
   - Add assertions to catch victim_addr[] corruption
   - Create minimal test case with single victim buffer
   - Trace exact cycle-by-cycle victim_addr[] value changes

## Files Modified

- `modelsim/harvard_cache_protected_tb.sv` - Fixed SDRAM latency and golden_write
- Analysis documented in this file

## Test Command

```bash
cd modelsim
python3 test_runner.py --test harvard_cache_protected
```

## Current Status

**Test Pass Rate**: 200/206 tests passing (97.1% across all tests)
**Harvard Cache**: 6 failures remaining (victim WB corruption)
**Commits Pushed**: 2 (SDRAM + golden_write fixes)

---

**Conclusion**: The remaining 6 failures are caused by a deep bug in victim_addr[] assignment or storage. The victim writeback mechanism writes to incorrect addresses, corrupting memory. Fixing this requires careful instrumentation and analysis of the victim buffer management logic.
