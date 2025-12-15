# DCache Non-Blocking Redesign - Full Architectural Specification

## Design Goals

1. **Non-blocking operation**: Service cache hits while handling misses/flushes in background
2. **Harvard architecture**: Maintain separate ICache and DCache
3. **Self-modifying code support**: DCache writes to code regions invalidate ICache
4. **Write-back policy**: Minimize memory traffic by buffering dirty data
5. **Hit-under-miss**: Continue serving hits during outstanding miss
6. **Background writeback**: Evicted dirty lines written back without blocking cache

## Architectural Overview

### Key Components

```
┌─────────────────────────────────────────────────────────────┐
│                      DCache Non-Blocking                     │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ Tag/Data RAM │  │ Tag/Data RAM │  │  Victim      │     │
│  │   Way 0      │  │   Way 1      │  │  Buffer      │     │
│  │  (512 sets)  │  │  (512 sets)  │  │  (2 entries) │     │
│  └──────────────┘  └──────────────┘  └──────────────┘     │
│                                                              │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ Fill Buffer  │  │ Write Buffer │  │   Memory     │     │
│  │ (1 entry)    │  │ (8 words)    │  │   Arbiter    │     │
│  └──────────────┘  └──────────────┘  └──────────────┘     │
│                                                              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │         Memory Request Queue (4 entries)             │  │
│  │  [FILL_REQ | VICTIM_WB | VICTIM_WB | EMPTY]          │  │
│  └──────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
```

### Data Structures

#### 1. Victim Buffer (2 entries)
```systemverilog
typedef struct packed {
    logic        valid;
    logic [19:4] addr;          // Cache line address
    logic [15:0] data [0:7];    // 8 words
    logic [2:0]  wb_progress;   // Writeback beat counter
    logic        wb_active;     // Currently writing back
} victim_entry_t;

victim_entry_t victim_buffer [0:1];
```

**Purpose**: Hold evicted dirty lines for background writeback without blocking cache

#### 2. Fill Buffer (1 entry)
```systemverilog
typedef struct packed {
    logic        valid;
    logic [19:1] addr;
    logic [15:0] data [0:7];
    logic [7:0]  words_valid;   // Bitmap of received words
    logic        way;
    logic [index_bits-1:0] index;
    logic [tag_bits-1:0]   tag;
} fill_buffer_t;

fill_buffer_t fill_buffer;
```

**Purpose**: Accumulate incoming cache line, enable early restart

#### 3. Memory Request Queue (4 entries)
```systemverilog
typedef enum logic [1:0] {
    REQ_NONE,
    REQ_FILL,
    REQ_VICTIM_WB
} mem_req_type_t;

typedef struct packed {
    mem_req_type_t req_type;
    logic [19:1]   addr;
    logic [1:0]    victim_id;   // Which victim buffer entry
} mem_req_t;

mem_req_t mem_req_queue [0:3];
logic [1:0] queue_head, queue_tail;
```

**Purpose**: Serialize memory requests, prevent conflicts

### Cache Line States

Each cache line has a state:

```systemverilog
typedef enum logic [2:0] {
    INVALID,        // Line not present
    VALID_CLEAN,    // Present, matches memory
    VALID_DIRTY,    // Present, modified
    PENDING_FILL,   // Fill in progress (miss being serviced)
    EVICTED         // Evicted to victim buffer
} cache_line_state_t;
```

### Operation Modes

#### Normal Hit
1. Tag match, state = VALID_CLEAN or VALID_DIRTY
2. Return data immediately (1-2 cycle latency)
3. Update LRU
4. If write: Mark VALID_DIRTY

#### Miss - Clean Eviction
1. Tag miss, LRU way is VALID_CLEAN
2. Invalidate LRU way immediately
3. Enqueue FILL request
4. Mark line PENDING_FILL
5. Continue servicing other hits

#### Miss - Dirty Eviction
1. Tag miss, LRU way is VALID_DIRTY
2. Capture dirty line to victim buffer
3. Mark line EVICTED (points to victim entry)
4. Enqueue VICTIM_WB request
5. Enqueue FILL request
6. Continue servicing other hits

#### Hit-Under-Miss
1. Ongoing fill for address A
2. Request for address B arrives
3. If B hits in cache: Service immediately
4. If B misses: Enqueue another FILL request
5. Multiple outstanding misses supported

#### Victim Buffer Writeback
1. Pop VICTIM_WB from queue
2. Write victim entry to memory (8 beats)
3. Mark victim entry invalid when complete
4. Process next queue entry

### Self-Modifying Code Support

**Coherence Protocol**:
1. DCache write to address A, check if A is in code region
2. If yes, schedule ICache invalidation via code_flush mechanism
3. ICache invalidation is asynchronous, doesn't block DCache

**Code Region Detection**: Already implemented in current design (MMIO detection logic)

### Memory Arbitration

**Priority** (highest to lowest):
1. Victim writeback (free up victim buffer)
2. Fill requests (reduce miss latency)
3. CPU read/write (if both caches idle)

**Queue Management**:
- 4-entry FIFO queue
- Enqueue: Add to tail if not full
- Dequeue: Process from head
- Stall: If queue full, stall allocation (but not hits!)

## Implementation Strategy

### Phase 1: Foundation (Week 1)
**Goal**: Add data structures without changing behavior

- [ ] Add victim_buffer[0:1] registers
- [ ] Add fill_buffer register
- [ ] Add mem_req_queue[0:3] registers
- [ ] Add cache_line_state array
- [ ] Initialize all in reset
- [ ] Test: No regression (5 mismatches baseline)

### Phase 2: Victim Buffer (Week 1-2)
**Goal**: Capture evicted lines to victim buffer

- [ ] Modify eviction logic to capture to victim
- [ ] Mark cache line EVICTED instead of INVALID
- [ ] Implement victim buffer allocation (round-robin)
- [ ] Test: Should still be blocking, no regression

### Phase 3: Memory Queue (Week 2)
**Goal**: Serialize memory requests

- [ ] Implement queue enqueue/dequeue logic
- [ ] Modify fill logic to use queue
- [ ] Modify flush logic to use queue
- [ ] Test: Still blocking, verify queue works

### Phase 4: Non-Blocking (Week 2-3)
**Goal**: Enable hit-under-miss

- [ ] Allow cache hits while PENDING_FILL active
- [ ] Implement fill buffer for incoming data
- [ ] Early restart: Hit on filling line
- [ ] Test: Should see improvement

### Phase 5: Background Writeback (Week 3)
**Goal**: Writeback victims in background

- [ ] Implement victim writeback FSM
- [ ] Process VICTIM_WB requests from queue
- [ ] Free victim entries when writeback done
- [ ] Test: Should see significant improvement

### Phase 6: Optimization (Week 3-4)
**Goal**: Fine-tune performance

- [ ] Optimize victim allocation
- [ ] Tune queue depth
- [ ] Add performance counters
- [ ] Test: Validate improvement

## Expected Performance Impact

### Current (Blocking)
- **Miss latency**: 16-24 cycles (flush + fill)
- **Cache blocked**: Entire miss duration
- **Throughput**: Serialized operations

### Target (Non-Blocking)
- **Miss latency**: 8-12 cycles (fill only, victim buffered)
- **Cache blocked**: 0 cycles (hits continue)
- **Throughput**: Multiple outstanding operations

### Test Prediction
- **Baseline**: 5 mismatches (blocking cache, 4-set test)
- **Target**: 0-1 mismatches (non-blocking cache)
- **Improvement**: ~80% reduction in blocking-related timeouts

## Risk Mitigation

1. **Incremental testing**: Test after each phase
2. **Rollback points**: Commit after each working phase
3. **Separate branch**: Keep original code intact
4. **Validation**: Run full test suite, not just harvard_cache_protected

## Success Criteria

- [ ] harvard_cache_protected test: ≤1 mismatches
- [ ] All other cache tests: No regressions
- [ ] FPU tests: No impact (165/165 passing)
- [ ] Timing closure: Still meets 50 MHz
- [ ] Resource usage: <85% ALMs (within budget)

---
**Author**: Claude (Sonnet 4.5)
**Date**: November 22, 2025
**Status**: Design phase complete, ready for implementation
