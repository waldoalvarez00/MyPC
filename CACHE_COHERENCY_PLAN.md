# Cache Coherency Implementation Plan
## Option 3: DMA/FPU Through Cache

**Date:** 2025-11-12
**Status:** Planning Phase
**Goal:** Eliminate data coherency issues by routing ALL memory accesses through the cache system

---

## Problem Statement

### Current Architecture (BROKEN - Coherency Issues)

```
CPU Instruction → ICache ──────────┐
                                   ├→ CacheArbiter → cache_unified_m_* ──┐
CPU Data → DCache ─────────────────┘                                     │
                                                                         │
                                            ┌────────────────────────────┘
                                            │
                                            ├→ PipelinedDMAFPUArbiter ──→ VGA Arbiter → SDRAM
                                            │
DMA ────────────────────────────────────────┤ (BYPASSES CACHE!)
                                            │
FPU ────────────────────────────────────────┘ (BYPASSES CACHE!)
```

### Coherency Violations

**Scenario 1: DMA Write → CPU Read (Stale CPU Data)**
```
1. CPU reads 0x1000 → cached in DCache
2. DMA writes 0x1000 → goes to SDRAM (bypasses cache)
3. CPU reads 0x1000 → gets OLD cached data ❌
```

**Scenario 2: CPU Write → FPU Read (Stale FPU Data)**
```
1. CPU writes 0x2000 → stays in DCache (write-back, dirty)
2. FPU reads 0x2000 → reads from SDRAM (bypasses cache)
3. FPU gets OLD data ❌
```

**Scenario 3: FPU Write → CPU Read (Stale CPU Data)**
```
1. CPU reads 0x3000 → cached in DCache
2. FPU writes 0x3000 → goes to SDRAM (bypasses cache)
3. CPU reads 0x3000 → gets OLD cached data ❌
```

---

## Proposed Solution: Route DMA/FPU Through DCache

### New Architecture (CORRECT - Coherency Guaranteed)

```
CPU Instruction → ICache ────────────────────────────────────┐
                                                             │
                                                             ├→ CacheArbiter → VGA Arbiter → SDRAM
CPU Data ────┐                                               │
             │                                               │
DMA ─────────┼→ DCacheFrontendArbiter (NEW) → DCache ───────┘
             │
FPU ─────────┘
```

**Key Changes:**
1. **Remove** PipelinedDMAFPUArbiter (no longer needed!)
2. **Create** DCacheFrontendArbiter (3-port: CPU, DMA, FPU)
3. **Route** all data memory accesses through DCache
4. **Simplify** arbiter chain (one less arbiter)

---

## Architecture Details

### DCacheFrontendArbiter (NEW MODULE)

**Purpose:** Multiplex CPU/DMA/FPU requests into the DCache frontend

**Interface:**
```systemverilog
module DCacheFrontendArbiter(
    input logic clk,
    input logic reset,

    // CPU Data Port (Priority: Lowest)
    input logic [19:1] cpu_addr,
    output logic [15:0] cpu_data_in,
    input logic [15:0] cpu_data_out,
    input logic cpu_access,
    output logic cpu_ack,
    input logic cpu_wr_en,
    input logic [1:0] cpu_bytesel,

    // DMA Port (Priority: Highest)
    input logic [19:1] dma_addr,
    output logic [15:0] dma_data_in,
    input logic [15:0] dma_data_out,
    input logic dma_access,
    output logic dma_ack,
    input logic dma_wr_en,
    input logic [1:0] dma_bytesel,

    // FPU Port (Priority: Medium)
    input logic [19:1] fpu_addr,
    output logic [15:0] fpu_data_in,
    input logic [15:0] fpu_data_out,
    input logic fpu_access,
    output logic fpu_ack,
    input logic fpu_wr_en,
    input logic [1:0] fpu_bytesel,

    // DCache Frontend (Single unified output)
    output logic [19:1] cache_addr,
    input logic [15:0] cache_data_in,
    output logic [15:0] cache_data_out,
    output logic cache_access,
    input logic cache_ack,
    output logic cache_wr_en,
    output logic [1:0] cache_bytesel
);
```

**Priority Scheme:**
- **Highest:** DMA (critical for floppy/disk transfers)
- **Medium:** FPU (avoid stalling floating-point operations)
- **Lowest:** CPU (most tolerant to delays due to prefetch/pipeline)

**Arbitration Logic:**
- State machine: IDLE, SERVING_DMA, SERVING_FPU, SERVING_CPU
- Serve one transaction at a time
- Return to IDLE on cache_ack
- Check DMA first, then FPU, then CPU

### Signal Flow Updates

**Current DCache Connections (mycore.sv lines 1123-1128):**
```systemverilog
// Direct CPU → DCache
assign dcache_c_addr = data_m_addr;
assign dcache_c_data_out = data_m_data_out;
assign dcache_c_access = data_m_access & ~d_io;
assign dcache_c_wr_en = data_m_wr_en;
assign dcache_c_bytesel = data_m_bytesel;
```

**New DCache Connections (via arbiter):**
```systemverilog
// CPU → DCacheFrontendArbiter
DCacheFrontendArbiter dcache_arbiter (
    .clk(sys_clk),
    .reset(post_sdram_reset),

    // CPU port
    .cpu_addr(data_m_addr),
    .cpu_data_in(data_m_data_in_from_cache),
    .cpu_data_out(data_m_data_out),
    .cpu_access(data_m_access & ~d_io),
    .cpu_ack(data_m_ack_from_cache),
    .cpu_wr_en(data_m_wr_en),
    .cpu_bytesel(data_m_bytesel),

    // DMA port (from KF8237-DMA)
    .dma_addr(dma_m_addr),
    .dma_data_in(dma_m_data_in),
    .dma_data_out(dma_m_data_out),
    .dma_access(dma_m_access & ~dma_d_io),  // Only memory, not I/O
    .dma_ack(dma_m_ack),
    .dma_wr_en(dma_m_wr_en),
    .dma_bytesel(dma_m_bytesel),

    // FPU port (from FPU_System_Integration)
    .fpu_addr(fpu_mem_addr[19:1]),  // Convert byte→word address
    .fpu_data_in(fpu_mem_data_in),
    .fpu_data_out(fpu_mem_data_out),
    .fpu_access(fpu_mem_access),
    .fpu_ack(fpu_mem_ack),
    .fpu_wr_en(fpu_mem_wr_en),
    .fpu_bytesel(fpu_mem_bytesel),

    // DCache frontend
    .cache_addr(dcache_c_addr),
    .cache_data_in(dcache_c_data_in),
    .cache_data_out(dcache_c_data_out),
    .cache_access(dcache_c_access),
    .cache_ack(dcache_c_ack),
    .cache_wr_en(dcache_c_wr_en),
    .cache_bytesel(dcache_c_bytesel)
);
```

### Removed Module

**PipelinedDMAFPUArbiter** - No longer needed!
- Previously: Muxed DMA/FPU/Cache → SDRAM
- Now: DMA/FPU go through cache, only ICache/DCache → SDRAM

---

## Coherency Analysis

### Problem 1: DMA Write → CPU Read
**Before:** DMA bypasses cache → CPU sees stale data
**After:**
```
1. DMA writes 0x1000 → DCacheFrontendArbiter → DCache
2. DCache invalidates old line, writes new data
3. CPU reads 0x1000 → DCache has correct data ✅
```

### Problem 2: CPU Write → FPU Read
**Before:** CPU writes to cache (write-back), FPU reads from SDRAM
**After:**
```
1. CPU writes 0x2000 → DCache (dirty)
2. FPU reads 0x2000 → DCacheFrontendArbiter → DCache
3. DCache serves from cache (dirty line) ✅
```
**OR** (if write-through):
```
1. CPU writes 0x2000 → DCache → writes through to SDRAM
2. FPU reads 0x2000 → DCache (cache hit) ✅
```

### Problem 3: FPU Write → CPU Read
**Before:** FPU bypasses cache → CPU sees stale data
**After:**
```
1. FPU writes 0x3000 → DCacheFrontendArbiter → DCache
2. DCache invalidates old line, writes new data
3. CPU reads 0x3000 → DCache has correct data ✅
```

**Result:** ✅ **All coherency problems solved!**

---

## Implementation Steps

### Phase 1: Create DCacheFrontendArbiter Module
**File:** `Quartus/rtl/common/DCacheFrontendArbiter.sv`

**Features:**
- 3-port arbiter (CPU, DMA, FPU)
- State machine with priority enforcement
- Registered outputs for glitch-free operation
- Minimal latency (1-cycle arbitration)

**Complexity:** ~200 lines (similar to CacheArbiter)

### Phase 2: Update mycore.sv Connections

**Remove:**
- PipelinedDMAFPUArbiter instantiation (lines 966-1013)
- cache_unified_m_* → PipelinedDMAFPUArbiter connections

**Add:**
- DCacheFrontendArbiter instantiation
- CPU/DMA/FPU → DCacheFrontendArbiter connections
- DCacheFrontendArbiter → DCache frontend connections

**Simplify:**
- CacheArbiter output now goes directly to VGA arbiter (not through DMA/FPU arbiter)

### Phase 3: Update Quartus Project
**File:** `Quartus/mycore.qsf`

**Add:**
```tcl
set_global_assignment -name SYSTEMVERILOG_FILE rtl/common/DCacheFrontendArbiter.sv
```

**Remove (optional - keep for reference):**
```tcl
# set_global_assignment -name SYSTEMVERILOG_FILE rtl/PipelinedDMAFPUArbiter.sv
```

### Phase 4: Create Coherency Tests
**File:** `modelsim/tb_cache_coherency.sv`

**Test Cases:**
1. DMA write → CPU read (verify CPU sees new data)
2. CPU write → FPU read (verify FPU sees new data)
3. FPU write → CPU read (verify CPU sees new data)
4. DMA write → FPU read (verify FPU sees new data)
5. Sequential DMA/FPU/CPU accesses (verify no stale data)
6. Overlapping cache lines (verify correct invalidation)

**Success Criteria:** All coherency tests pass with correct data

### Phase 5: Performance Testing
**File:** `modelsim/tb_cache_arbiter_performance.sv`

**Metrics:**
- Cache hit rate (should remain high: 90-95%)
- DMA throughput (should not degrade significantly)
- FPU memory latency (acceptable: 2-5 cycles for cache hit)
- CPU performance (should be similar or better)

---

## Performance Analysis

### Cache Hit Rate Impact

**CPU:** No change (same cache access pattern)
**DMA:** May increase cache pollution (DMA data is often not reused)
**FPU:** Likely benefits from caching (FPU often reuses data)

**Mitigation:**
- Consider write-through for DMA (don't pollute cache)
- Use LRU replacement (already implemented in DCache2Way)
- Monitor cache hit rate in testing

### Latency Comparison

**Before (DMA/FPU bypass cache):**
- DMA write: 8-16 cycles (SDRAM direct)
- FPU read: 8-16 cycles (SDRAM direct)
- CPU cache hit: 1-2 cycles

**After (DMA/FPU through cache):**
- DMA write (cache hit): 1-2 cycles ✅ (faster!)
- DMA write (cache miss): 10-20 cycles ❌ (slower, but rare)
- FPU read (cache hit): 1-2 cycles ✅ (much faster!)
- FPU read (cache miss): 10-20 cycles (same as before)
- CPU cache hit: 1-2 cycles (unchanged)

**Net Result:** FPU benefits significantly, DMA sees mixed impact

### Throughput Analysis

**Arbiter Overhead:**
- DCacheFrontendArbiter: 1 cycle per arbitration
- Cache access: 1-2 cycles for hit, 8-16 for miss
- Total: 2-3 cycles for hit, 9-17 for miss

**Contention:**
- CPU + FPU: Low contention (FPU memory access is rare)
- CPU + DMA: Medium contention (DMA is bursty)
- DMA + FPU: Very low contention (rarely simultaneous)

**Expected:** <5% performance degradation, with coherency correctness

---

## Design Decisions

### Decision 1: Write Policy for DMA

**Options:**
1. **Write-through:** DMA writes go through cache but always update SDRAM
   - Pros: Simple, doesn't pollute cache with one-time data
   - Cons: Slower for repeated DMA writes

2. **Write-back:** DMA writes stay in cache (dirty)
   - Pros: Faster for repeated accesses
   - Cons: Cache pollution, delayed writeback

**Recommendation:** **Write-through for DMA** (implement as a flag to DCache)

### Decision 2: Cache Allocation Policy

**Options:**
1. **Allocate on write:** DMA writes allocate cache lines
   - Pros: Subsequent reads are fast
   - Cons: Cache pollution

2. **No allocate on write:** DMA writes bypass cache allocation
   - Pros: No cache pollution
   - Cons: More complex

**Recommendation:** **Allocate on write** (simpler, let LRU handle eviction)

### Decision 3: Priority Scheme

**Chosen:** DMA > FPU > CPU

**Rationale:**
- DMA must complete without interruption (critical for I/O)
- FPU operations are long-running (minimize stalls)
- CPU has prefetch and can tolerate short delays

---

## Testing Strategy

### Unit Tests
1. **DCacheFrontendArbiter alone**
   - Test priority enforcement
   - Test data routing
   - Test ACK generation

2. **DCache with arbiter**
   - Test cache hits with multiple requestors
   - Test cache misses with multiple requestors
   - Test write-back/write-through

### Integration Tests
1. **Coherency scenarios** (critical!)
   - DMA write → CPU read
   - CPU write → FPU read
   - FPU write → CPU read
   - Mixed sequences

2. **Performance benchmarks**
   - CPU-only workload
   - DMA transfer throughput
   - FPU memory access latency

### Hardware Validation
1. **Floppy DMA test**
   - Read sector via DMA
   - Verify CPU sees correct data
   - Compare with old implementation

2. **FPU matrix operations**
   - Load matrix from memory (FILD)
   - Perform calculations
   - Store result (FISTP)
   - Verify no stale data

---

## Risks and Mitigation

### Risk 1: Performance Degradation
**Impact:** DMA/FPU slower due to cache overhead
**Likelihood:** Medium
**Mitigation:**
- Benchmark before/after
- Optimize arbiter for low latency
- Consider write-through for DMA

### Risk 2: Cache Pollution
**Impact:** CPU cache hit rate drops due to DMA/FPU
**Likelihood:** Low (LRU replacement helps)
**Mitigation:**
- Monitor cache hit rate
- Consider separate cache ways for DMA/FPU (future)

### Risk 3: Increased Complexity
**Impact:** More difficult to debug
**Likelihood:** Low
**Mitigation:**
- Comprehensive testing
- Clear documentation
- Performance counters for monitoring

---

## Success Criteria

1. ✅ **Coherency:** All coherency test cases pass (100%)
2. ✅ **Functionality:** All existing tests still pass
3. ✅ **Performance:** <10% degradation vs. bypass architecture
4. ✅ **Correctness:** Floppy DMA and FPU operations work correctly

---

## Timeline Estimate

- **Phase 1 (Arbiter):** 2-3 hours
- **Phase 2 (Integration):** 1-2 hours
- **Phase 3 (Project update):** 15 minutes
- **Phase 4 (Testing):** 3-4 hours
- **Phase 5 (Performance):** 1-2 hours

**Total:** 7-11 hours (1-2 work days)

---

## Alternative Considered: Cache Invalidation (Option 1)

**Why not chosen:**
- More complex (need invalidation logic in cache)
- Doesn't solve CPU write → FPU read (need flush too)
- Partial solution (doesn't help FPU performance)

**Option 3 advantages:**
- Complete solution (solves all coherency issues)
- Simpler architecture (fewer arbiters)
- Performance benefit for FPU (caching!)
- Proven approach (used in real CPUs)

---

## References

- Original coherency issue identification: User feedback
- Current architecture: `Quartus/mycore.sv` lines 966-1175
- Cache implementation: `Quartus/rtl/common/DCache2Way.sv`
- Arbiter reference: `Quartus/rtl/common/CacheArbiter.sv`

---

**Document Status:** Planning Complete - Ready for Implementation
**Next Step:** Implement DCacheFrontendArbiter.sv
