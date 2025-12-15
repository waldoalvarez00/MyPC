# DCache2Way Non-Blocking Cache Refactoring Plan

## Executive Summary

**Objective**: Transform DCache2Way from a blocking cache architecture (one operation at a time) to a non-blocking cache that can service reads during flush/fill operations.

**Motivation**:
- Eliminate read stalls during flush operations (currently 8+ cycles blocked)
- Improve cache throughput by 15-25% under high conflict scenarios
- Fix `harvard_cache_protected` test failures without artificial limitations

**Complexity**: Major architectural refactoring
**Estimated Effort**: 2-3 weeks (1 week design/prototyping, 1 week implementation, 1 week testing/validation)
**Risk Level**: High (cache is critical path for performance and correctness)

---

## Current Architecture Analysis

### Blocking Behavior

**Current State Machine** (simplified):
```
IDLE → FILL (8 cycles) → IDLE
IDLE → FLUSH (8 cycles) → FILL (8 cycles) → IDLE
```

During FILL or FLUSH: `busy=1`, all new requests blocked.

**Key Blocking Points**:
1. **Line 230-231**: `hit_way0/1` require `!busy`
2. **Line 254**: `c_ack` blocked by `!flushing_active`
3. **Line 603**: `latched_address` update blocked when `busy || flushing_active`

### Port Usage

**BlockRAM Dual Ports**:
- **Port A**: Cache reads/writes (address: `c_addr[index_end:1]`)
- **Port B**: Fill/flush operations (address: `line_addr_for_b`)

**Current Conflict Avoidance**: Serialize all operations (only use one port at a time).

**Problem**: Port B is dedicated to flush/fill, blocking Port A usage unnecessarily.

---

## Non-Blocking Architecture Design

### Design Principles

1. **Decouple Flush from Cache Access**: Flush operates on separate buffer, not BlockRAM directly
2. **Read Priority**: Cache hits take priority over flush operations
3. **Hazard Detection**: Prevent reads to line currently being flushed/filled
4. **Minimal State**: Avoid complex FSM; use simple hazard flags

### Key Components to Add

#### 1. Flush Buffer (New)

**Purpose**: Capture dirty line data for background writeback

```systemverilog
// Flush buffer - holds one dirty cache line during writeback
logic [15:0] flush_buffer [0:7];  // 8 words = 1 cache line
logic [2:0]  flush_buffer_valid;  // Which words are valid
logic [19:4] flush_buffer_addr;   // Base address of buffered line
logic        flush_buffer_active; // Buffer contains valid data
```

**Operation**:
1. On eviction: Copy dirty line from BlockRAM to `flush_buffer` (1 cycle using port B)
2. Writeback: Send buffer contents to memory (8 cycles, independent of BlockRAM)
3. Cache available: BlockRAM port A/B free for normal operations during writeback

#### 2. Miss Status Holding Register (MSHR)

**Purpose**: Track outstanding fill operations

```systemverilog
typedef struct packed {
    logic        valid;          // MSHR entry is active
    logic [19:1] addr;           // Address being filled
    logic [2:0]  words_filled;   // Bitmap of filled words (0-7)
    logic        way;            // Which way is being filled
    logic [index_bits-1:0] index; // Cache set index
} mshr_t;

mshr_t mshr;  // Single MSHR entry for simplicity
```

**Operation**:
1. On cache miss: Allocate MSHR entry
2. During fill: Update `words_filled` as data arrives
3. On completion: Mark MSHR invalid, update cache metadata

#### 3. Hazard Detection Logic

**Purpose**: Prevent read/write conflicts during concurrent operations

```systemverilog
// Hazard detection
wire addr_matches_flush = c_addr[19:4] == flush_buffer_addr && flush_buffer_active;
wire addr_matches_mshr  = c_addr[19:4] == mshr.addr[19:4] && mshr.valid;

// Allow operation if no hazards
wire no_structural_hazard = !addr_matches_flush && !addr_matches_mshr;
```

### Modified State Machine

**New Overlapped Operation Model**:
```
States:
  - IDLE: No operations
  - FILLING: Fill in progress (MSHR active)
  - FLUSHING: Writeback in progress (flush_buffer active)
  - FILLING_AND_FLUSHING: Both operations concurrent

Transitions:
  IDLE → FILLING (on miss)
  IDLE → FLUSHING (on dirty eviction)
  FILLING → FILLING_AND_FLUSHING (dirty eviction during fill)
  FLUSHING → FILLING_AND_FLUSHING (miss during flush)
```

**Key Difference**: States are NOT mutually exclusive! Can fill while flushing.

---

## Detailed Implementation Plan

### Phase 1: Design and Prototyping (Week 1)

#### Milestone 1.1: Flush Buffer Design (Days 1-2)

**Tasks**:
1. Define flush buffer structure in DCache2Way.sv
2. Add buffer allocation logic (on dirty eviction)
3. Add buffer writeback FSM (independent of main cache FSM)
4. Add buffer de-allocation logic (on writeback complete)

**Files Modified**:
- `Quartus/rtl/common/DCache2Way.sv`

**New Code Sections**:
```systemverilog
// Flush buffer declaration (after line 117)
logic [15:0] flush_buffer [0:7];
logic [19:4] flush_buffer_addr;
logic        flush_buffer_active;
logic [2:0]  flush_buffer_beat;  // Current word being written back

// Flush buffer FSM (new section around line 720)
typedef enum logic [1:0] {
    FB_IDLE,      // No flush in progress
    FB_COPY,      // Copying line from BlockRAM to buffer (1 cycle)
    FB_WRITEBACK  // Writing buffer to memory (8 cycles)
} flush_buffer_state_t;

flush_buffer_state_t fb_state;

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        fb_state <= FB_IDLE;
        flush_buffer_active <= 1'b0;
        flush_buffer_beat <= 3'b0;
    end else begin
        case (fb_state)
            FB_IDLE: begin
                // Allocate buffer on dirty eviction
                if (request_flush_dirty) begin
                    fb_state <= FB_COPY;
                    flush_buffer_addr <= /* evicted line address */;
                end
            end

            FB_COPY: begin
                // Capture all 8 words from BlockRAM port B in single cycle
                // (requires reading entire line through burst or parallel read)
                for (int i = 0; i < 8; i++) begin
                    flush_buffer[i] <= /* read from BlockRAM */;
                end
                flush_buffer_active <= 1'b1;
                fb_state <= FB_WRITEBACK;
                flush_buffer_beat <= 3'b0;
            end

            FB_WRITEBACK: begin
                if (m_ack) begin
                    flush_buffer_beat <= flush_buffer_beat + 1;
                    if (flush_buffer_beat == 3'b111) begin
                        fb_state <= FB_IDLE;
                        flush_buffer_active <= 1'b0;
                    end
                end
            end
        endcase
    end
end
```

**Challenges**:
- **BlockRAM Read Latency**: Capturing full line requires 8 cycles OR redesign BlockRAM interface
- **Solution**: Add wide read port to BlockRAM (read entire line in 1 cycle) OR use sequential capture with stall

**Decision Point**: Choose between:
1. **Wide Read Port**: Modify BlockRAM to support 128-bit read (8×16-bit words) - COMPLEX
2. **Sequential Capture**: Accept 8-cycle capture before writeback begins - SIMPLE
3. **Interleaved Capture**: Start writeback after first word captured - OPTIMAL

**Recommendation**: Option 3 (Interleaved Capture) - best balance

#### Milestone 1.2: MSHR Design (Days 2-3)

**Tasks**:
1. Define MSHR structure
2. Add MSHR allocation on cache miss
3. Add MSHR update during fill
4. Add MSHR completion and metadata update logic

**New Code Sections**:
```systemverilog
// MSHR declaration (after flush buffer)
typedef struct packed {
    logic        valid;
    logic [19:1] addr;
    logic [7:0]  words_filled;  // Bitmap: which words have arrived
    logic        way;           // 0 or 1
    logic [index_bits-1:0] index;
} mshr_t;

mshr_t mshr;

// MSHR allocation (modify fill logic around line 685)
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        mshr.valid <= 1'b0;
    end else begin
        if (request_fill && !mshr.valid) begin
            // Allocate MSHR
            mshr.valid <= 1'b1;
            mshr.addr <= c_addr;
            mshr.way <= way_to_replace;
            mshr.index <= c_addr[index_end:index_start];
            mshr.words_filled <= 8'h00;  // None filled yet
        end

        if (mshr.valid && m_ack && !flushing_active) begin
            // Update bitmap as words arrive
            mshr.words_filled[line_idx] <= 1'b1;

            // Complete when all 8 words filled
            if (mshr.words_filled == 8'hFF) begin
                mshr.valid <= 1'b0;
                // Update cache valid/tag metadata here
            end
        end
    end
end
```

**Challenges**:
- **Early Tag Update**: When to set tag/valid for partially filled line?
- **Solution**: Set tag/valid on MSHR allocation, allow early hits as words arrive

#### Milestone 1.3: Hazard Detection (Day 3)

**Tasks**:
1. Implement address matching logic
2. Add hazard checks to hit detection
3. Add hazard checks to new request processing

**New Code Sections**:
```systemverilog
// Hazard detection (around line 200, before hit logic)
wire flush_hazard = c_addr[19:4] == flush_buffer_addr && flush_buffer_active;
wire fill_hazard  = c_addr[19:4] == mshr.addr[19:4] && mshr.valid;
wire structural_hazard = flush_hazard || fill_hazard;

// Modified hit detection to account for hazards
wire can_hit_normally = !busy || (mshr.valid && c_addr[19:4] == mshr.addr[19:4]);
assign hit_way0 = (accessing && valid_way0 && tags_match_way0 && can_hit_normally && !flush_hazard) || early_hit_way0;
assign hit_way1 = (accessing && valid_way1 && tags_match_way1 && can_hit_normally && !flush_hazard) || early_hit_way1;
```

#### Milestone 1.4: Integration Design (Days 4-5)

**Tasks**:
1. Design memory interface arbiter (flush vs fill)
2. Design c_ack generation with concurrent operations
3. Create state transition diagram for all cases
4. Document port usage in all states

**Memory Interface Arbiter**:
```systemverilog
// Memory request arbiter
typedef enum logic [1:0] {
    MEM_IDLE,
    MEM_FLUSH,  // Flush buffer has priority
    MEM_FILL    // Fill operations
} mem_owner_t;

mem_owner_t mem_owner;

always_comb begin
    // Priority: Flush > Fill
    if (fb_state == FB_WRITEBACK) begin
        m_addr = {flush_buffer_addr, flush_buffer_beat};
        m_data_out = flush_buffer[flush_buffer_beat];
        m_wr_en = 1'b1;
        m_access = 1'b1;
    end else if (mshr.valid) begin
        m_addr = {mshr.addr[19:4], line_idx};
        m_wr_en = 1'b0;
        m_access = 1'b1;
    end else begin
        m_access = 1'b0;
        // ... existing logic for non-fill/flush operations
    end
end
```

### Phase 2: Implementation (Week 2)

#### Milestone 2.1: Flush Buffer Implementation (Days 6-7)

**Tasks**:
1. Implement flush buffer structure
2. Implement buffer allocation on dirty eviction
3. Implement writeback FSM
4. Connect to memory interface

**Testing Strategy**:
- Unit test: Verify buffer captures dirty line correctly
- Unit test: Verify writeback sends correct data to memory
- Integration test: Verify cache still functions with buffer (no concurrent ops yet)

**Regression Guard**:
```bash
# After each change, run:
cd modelsim && python3 test_runner.py --test dcache2way_flush
cd modelsim && python3 test_runner.py --test harvard_dcache_flush
```

#### Milestone 2.2: MSHR Implementation (Days 8-9)

**Tasks**:
1. Implement MSHR structure and allocation
2. Implement word-by-word fill tracking
3. Implement early hit during fill (read words already arrived)
4. Update cache metadata on fill completion

**Testing Strategy**:
- Unit test: Verify MSHR allocation on miss
- Unit test: Verify word tracking during fill
- Unit test: Verify early hits to partially filled line
- Integration test: Verify cache coherence after fill completes

**Regression Guard**:
```bash
cd modelsim && python3 test_runner.py --test harvard_cache
cd modelsim && python3 test_runner.py --test cache
```

#### Milestone 2.3: Hazard Detection Implementation (Day 10)

**Tasks**:
1. Implement address matching logic
2. Add hazard blocking to hit detection
3. Add hazard detection to request processing
4. Add debug prints for hazard events

**Testing Strategy**:
- Unit test: Verify flush hazard detection
- Unit test: Verify fill hazard detection
- Unit test: Verify requests blocked when hazards present
- Stress test: Random operations with intentional hazards

**Debug Instrumentation**:
```systemverilog
if (DEBUG && structural_hazard) begin
    $display("[%0t][DCache2Way] HAZARD: c_addr=%h flush_hazard=%b fill_hazard=%b blocked",
             $time, c_addr, flush_hazard, fill_hazard);
end
```

#### Milestone 2.4: Concurrent Operations (Days 11-12)

**Tasks**:
1. Implement memory arbiter (flush vs fill priority)
2. Enable simultaneous flush and fill operations
3. Implement c_ack generation during concurrent operations
4. Handle edge cases (flush completes during fill, etc.)

**Testing Strategy**:
- Stress test: Trigger flush during ongoing fill
- Stress test: Trigger fill during ongoing flush
- Verify both complete correctly
- Verify cache consistency maintained

### Phase 3: Testing and Validation (Week 3)

#### Milestone 3.1: Unit Testing (Days 13-14)

**Create Comprehensive Test Suite**:

1. **Test: Flush During Read**
   - Fill cache with dirty data
   - Trigger eviction (flush starts)
   - Issue read to different cache line
   - **Expected**: Read completes during flush, correct data returned

2. **Test: Fill During Read**
   - Trigger cache miss (fill starts)
   - Issue read to different cached line
   - **Expected**: Read completes during fill, correct data returned

3. **Test: Concurrent Flush and Fill**
   - Trigger miss causing dirty eviction
   - **Expected**: Fill and flush proceed concurrently, both complete

4. **Test: Hazard Detection**
   - Start flush of address X
   - Issue read to same address X
   - **Expected**: Read blocked until flush completes

5. **Test: Port Conflict Avoidance**
   - Verify port A and port B never conflict
   - Verify correct data routing in all scenarios

**New Test Files**:
- `modelsim/dcache_nonblocking_flush_tb.sv`
- `modelsim/dcache_nonblocking_fill_tb.sv`
- `modelsim/dcache_nonblocking_concurrent_tb.sv`
- `modelsim/dcache_nonblocking_hazard_tb.sv`

#### Milestone 3.2: Integration Testing (Day 15)

**Run Full Test Suite**:
```bash
# Memory tests (should all pass now, including harvard_cache_protected)
python3 test_runner.py --category memory --verbose

# Full regression
python3 test_runner.py --parallel 4
```

**Expected Improvements**:
- `harvard_cache_protected`: Should now PASS (was 5 failures)
- All other memory tests: Continue to pass
- No regressions in other test categories

#### Milestone 3.3: Performance Validation (Day 16)

**Benchmarking**:

1. **Flush Blocking Time**:
   - Before: 8+ cycles (all ops blocked)
   - After: 0 cycles (reads continue during flush)
   - **Improvement**: 100% reduction in flush stall time

2. **Cache Miss Penalty**:
   - Before: 8 cycles fill + potential flush delay
   - After: 8 cycles fill (flush happens in parallel)
   - **Improvement**: Eliminate serialization penalty

3. **Overall Throughput**:
   - Measure ops/cycle under high conflict rate
   - Expected improvement: 15-25% for small caches, 5-10% for large caches

**Benchmark Test**:
```systemverilog
// modelsim/dcache_benchmark_tb.sv
// Generate random read/write/eviction patterns
// Measure total cycles to complete N operations
// Compare blocking vs non-blocking implementations
```

#### Milestone 3.4: Timing Closure (Days 17-18)

**FPGA Synthesis**:
1. Synthesize modified DCache2Way in Quartus
2. Check timing reports
3. Verify 50 MHz clock still achievable
4. Check area utilization increase

**Expected Impact**:
- **Logic**: +10-15% ALMs (flush buffer, MSHR, hazard logic)
- **Memory**: +128 bits (flush buffer = 8×16-bit words)
- **Timing**: Potential critical path in hazard detection

**Mitigation if Timing Fails**:
- Pipeline hazard detection (add 1-cycle latency)
- Simplify MSHR logic (reduce word tracking granularity)
- Reduce flush buffer depth (trade performance for timing)

### Phase 4: Deployment (Days 19-21)

#### Milestone 4.1: Documentation (Day 19)

**Update Documentation**:

1. **CLAUDE.md**:
   - Update "Known Issues" section (remove harvard_cache_protected failure)
   - Update cache architecture description
   - Add performance characteristics

2. **Code Comments**:
   - Document flush buffer operation
   - Document MSHR operation
   - Document hazard detection logic
   - Add ASCII art diagrams of state transitions

3. **Architecture Document**:
   - Create `docs/DCACHE_NON_BLOCKING_ARCHITECTURE.md`
   - Explain design decisions
   - Document performance tradeoffs
   - Provide debugging guide

#### Milestone 4.2: Code Review Preparation (Day 20)

**Prepare for Review**:
1. Self-review all changes
2. Ensure debug prints are consistent
3. Verify all tests pass
4. Create before/after comparison document
5. Prepare demo showing concurrent operations

**Review Checklist**:
- [ ] All unit tests pass
- [ ] All integration tests pass
- [ ] Full regression passes (no new failures)
- [ ] Timing closure achieved at 50 MHz
- [ ] Area increase acceptable (<10% total FPGA)
- [ ] Documentation complete
- [ ] Code follows project style
- [ ] Debug instrumentation in place

#### Milestone 4.3: Merge and Deploy (Day 21)

**Merge Process**:
1. Create pull request with detailed description
2. Address review comments
3. Final regression test on latest main branch
4. Merge to main
5. Tag release with version bump

---

## Risk Analysis and Mitigation

### High Risk Areas

#### Risk 1: Data Corruption

**Scenario**: Concurrent operations cause incorrect data to be read/written

**Mitigation**:
- Extensive hazard detection
- Conservative approach: block on any uncertainty
- Comprehensive testing with random patterns
- Add assertions in RTL to catch corruption

**Detection**:
```systemverilog
// Assertion: Never allow concurrent access to same address
assert property (@(posedge clk) disable iff (reset)
    !(c_access && flush_buffer_active && c_addr[19:4] == flush_buffer_addr)
) else $error("Flush hazard violation!");
```

#### Risk 2: Timing Closure Failure

**Scenario**: Additional logic creates critical path >50 MHz

**Mitigation**:
- Early synthesis checks (after Phase 1)
- Pipeline hazard logic if needed
- Simplify MSHR if needed
- Accept small performance loss for timing

**Fallback Plan**: Revert to blocking cache if timing cannot be met

#### Risk 3: Increased Complexity

**Scenario**: Non-blocking logic is too complex to maintain/debug

**Mitigation**:
- Extensive documentation
- Debug instrumentation from day 1
- Regular self-review sessions
- Incremental implementation (test each component)

**Complexity Metrics**:
- Lines of code: +300-400 lines in DCache2Way.sv
- State machine states: +3-4 states
- Concurrent state combinations: ~10 valid combinations

### Medium Risk Areas

#### Risk 4: BlockRAM Port Conflicts

**Scenario**: Port A and Port B try to access same location simultaneously

**Mitigation**:
- Careful port usage documentation
- Hazard detection prevents conflicts
- BlockRAM has built-in bypass logic for write conflicts

#### Risk 5: MSHR State Inconsistency

**Scenario**: MSHR gets out of sync with cache state

**Mitigation**:
- Single MSHR simplifies state management
- Clear allocation/deallocation points
- Assertion checks for MSHR validity

---

## Testing Strategy

### Unit Tests (Component Level)

1. **Flush Buffer Tests**:
   - Test buffer allocation on dirty eviction
   - Test buffer writeback to memory
   - Test buffer deallocation after writeback
   - Test multiple sequential flushes

2. **MSHR Tests**:
   - Test MSHR allocation on miss
   - Test word-by-word fill tracking
   - Test MSHR deallocation on completion
   - Test early hits during fill

3. **Hazard Detection Tests**:
   - Test flush hazard detection and blocking
   - Test fill hazard detection and blocking
   - Test hazard resolution (operation proceeds after hazard clears)

### Integration Tests (System Level)

1. **Concurrent Operations**:
   - Fill during flush
   - Flush during fill
   - Multiple sequential operations
   - Random operation sequences

2. **Stress Tests**:
   - 1000+ random operations
   - High conflict rate (small cache)
   - Back-to-back evictions
   - Pathological access patterns

3. **Regression Tests**:
   - All existing cache tests must pass
   - harvard_cache_protected must pass
   - No performance regression on existing tests

### Performance Tests

1. **Throughput Benchmark**:
   - Measure ops/cycle under various conditions
   - Compare blocking vs non-blocking
   - Test with 4, 16, 64, 256 sets

2. **Latency Benchmark**:
   - Measure average read latency
   - Measure worst-case read latency
   - Measure impact of concurrent flush

### Validation Criteria

**Must Pass**:
- All unit tests (100% pass)
- All integration tests (100% pass)
- All regression tests (100% pass)
- Timing closure at 50 MHz
- Area increase <15%

**Should Achieve**:
- harvard_cache_protected test passes
- Throughput improvement: 10-20%
- Latency improvement: 20-30% (worst case)

---

## Resource Estimates

### Hardware Resources

**Logic (ALMs)**:
- Flush buffer FSM: ~50 ALMs
- MSHR logic: ~100 ALMs
- Hazard detection: ~30 ALMs
- Memory arbiter: ~40 ALMs
- **Total**: ~220 ALMs (~0.3% of Cyclone V)

**Memory (Bits)**:
- Flush buffer: 8×16 = 128 bits
- MSHR: ~50 bits
- **Total**: ~180 bits (negligible)

**Expected Total Impact**: +10-15% of current DCache2Way size

### Development Resources

**Time Breakdown**:
- Week 1 (Design): 40 hours
  - Flush buffer design: 16 hours
  - MSHR design: 12 hours
  - Hazard detection: 8 hours
  - Integration design: 4 hours

- Week 2 (Implementation): 40 hours
  - Flush buffer impl: 12 hours
  - MSHR impl: 12 hours
  - Hazard detection impl: 8 hours
  - Integration: 8 hours

- Week 3 (Testing): 40 hours
  - Unit testing: 16 hours
  - Integration testing: 12 hours
  - Performance validation: 8 hours
  - Timing closure: 4 hours

- Week 4 (Buffer): 16 hours
  - Documentation: 8 hours
  - Review prep: 4 hours
  - Contingency: 4 hours

**Total**: 136 hours (~3.5 weeks full-time)

---

## Success Criteria

### Functional Requirements

✅ **Must Have**:
1. Cache hits proceed during flush operations (no blocking)
2. Cache fills proceed during flush operations (concurrent)
3. Hazard detection prevents data corruption
4. All existing tests continue to pass
5. harvard_cache_protected test passes

✅ **Should Have**:
1. Throughput improvement: 15-25% (small cache), 5-10% (large cache)
2. Worst-case read latency: <10 cycles (vs current >50 during flush)
3. Area increase: <10% total cache size
4. Timing closure: 50 MHz maintained

✅ **Nice to Have**:
1. Support for multiple outstanding fills (2+ MSHR entries)
2. Prefetch support for sequential accesses
3. Configurable flush buffer depth

### Performance Targets

| Metric | Current | Target | Stretch |
|--------|---------|--------|---------|
| Flush blocking time | 8+ cycles | 0 cycles | 0 cycles |
| Concurrent ops | No | Yes | Yes + prefetch |
| Harvard_cache_protected | 5 fails | 0 fails | 0 fails |
| Throughput (4-set) | Baseline | +20% | +30% |
| Throughput (256-set) | Baseline | +5% | +10% |
| Area (ALMs) | Baseline | +15% | +10% |

---

## Rollback Plan

If non-blocking implementation fails or causes issues:

### Rollback Triggers

1. **Timing Failure**: Cannot achieve 50 MHz after 2 optimization attempts
2. **Area Explosion**: >20% increase in FPGA utilization
3. **Data Corruption**: Random failures that cannot be debugged in 3 days
4. **Schedule Overrun**: Week 4 ends with <80% tests passing

### Rollback Procedure

1. Revert DCache2Way.sv to blocking version
2. Document lessons learned
3. Consider simpler alternative (Victim Buffer option)
4. Update CLAUDE.md with updated analysis

### Fallback Architecture

If non-blocking proves too complex, implement **Victim Buffer** (simpler alternative):
- 90% of benefit, 30% of complexity
- 1-2 entry buffer for evicted lines
- Flush from buffer in background
- Much simpler state machine

---

## Appendix A: Code Structure

### New Files to Create

```
modelsim/
  dcache_nonblocking_flush_tb.sv       (flush during read test)
  dcache_nonblocking_fill_tb.sv        (fill during read test)
  dcache_nonblocking_concurrent_tb.sv  (concurrent ops test)
  dcache_nonblocking_hazard_tb.sv      (hazard detection test)
  dcache_benchmark_tb.sv               (performance benchmark)

docs/
  DCACHE_NON_BLOCKING_ARCHITECTURE.md  (architecture doc)
  DCACHE_NON_BLOCKING_DEBUGGING.md     (debug guide)
```

### Modified Files

```
Quartus/rtl/common/DCache2Way.sv  (+400 lines, major changes)
modelsim/test_configs.py          (add new tests)
modelsim/test_runner.py           (no changes needed)
CLAUDE.md                         (update known issues, architecture)
```

---

## Appendix B: Key Design Decisions

### Decision 1: Single MSHR vs Multiple MSHRs

**Chosen**: Single MSHR
**Rationale**:
- Simplicity (one outstanding fill at a time)
- Sufficient for most workloads
- Easier to debug and verify
- Can extend to multiple later if needed

**Tradeoff**: Cannot handle multiple simultaneous misses (rare in 2-way cache)

### Decision 2: Flush Buffer Depth

**Chosen**: Single cache line (8 words)
**Rationale**:
- Handles most common case (one dirty eviction)
- Minimal area overhead
- Simple state machine

**Tradeoff**: Cannot handle multiple simultaneous evictions (accept stall in rare case)

### Decision 3: Memory Arbitration Priority

**Chosen**: Flush > Fill
**Rationale**:
- Flush frees up buffer for next eviction
- Fill can tolerate slight delay (miss already incurred)
- Prevents buffer overflow

**Alternative Considered**: Fill > Flush (rejected: could cause buffer stall)

### Decision 4: Hazard Handling

**Chosen**: Block request until hazard clears
**Rationale**:
- Simplest correct solution
- Rare in practice (accessing line being flushed/filled)
- Clear to reason about

**Alternative Considered**: Forward from buffer (complex, error-prone)

---

## Appendix C: Testing Checklist

### Pre-Implementation Tests (Baseline)

- [ ] Run full test suite, record pass rate
- [ ] Run harvard_cache_protected, record failures (expect 5)
- [ ] Run performance benchmark, record baseline
- [ ] Synthesize current design, record area/timing

### Phase 1 Tests (After Flush Buffer)

- [ ] Flush buffer allocation test
- [ ] Flush buffer writeback test
- [ ] Regression: dcache2way_flush (must pass)
- [ ] Regression: harvard_dcache_flush (must pass)

### Phase 2 Tests (After MSHR)

- [ ] MSHR allocation test
- [ ] MSHR fill tracking test
- [ ] Early hit during fill test
- [ ] Regression: harvard_cache (must pass)
- [ ] Regression: cache (must pass)

### Phase 3 Tests (After Integration)

- [ ] Concurrent flush+fill test
- [ ] Flush during read test
- [ ] Fill during read test
- [ ] Hazard detection test
- [ ] **Critical**: harvard_cache_protected (expect 0 failures!)
- [ ] Full regression (all tests must pass)

### Phase 4 Tests (Final Validation)

- [ ] Performance benchmark (verify improvements)
- [ ] Synthesis (verify timing/area)
- [ ] Stress test (1000+ random ops, multiple runs)
- [ ] Code review checklist complete

---

## Contact and Questions

**Questions During Implementation**:
- Architectural decisions: Review with team lead
- Timing issues: Consult FPGA synthesis expert
- Test failures: Review test logs, add debug prints

**Progress Tracking**:
- Daily standup: Report milestone progress
- Weekly review: Demo working functionality
- Blocker escalation: If stuck >4 hours on issue

**Document Maintenance**:
- Update this plan as decisions change
- Document deviations from plan with rationale
- Keep lessons learned log for future projects

---

**Last Updated**: 2025-11-22
**Author**: Claude (AI Assistant)
**Status**: Planning Document - Not Yet Implemented
