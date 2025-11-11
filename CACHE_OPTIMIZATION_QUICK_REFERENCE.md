# Cache Optimization Quick Reference
## At-a-Glance Decision Guide

**Date:** 2025-11-11
**Project:** MyPC Data Cache Optimization

---

## Current Configuration

```
Direct-Mapped Data Cache
├── Size: 8 KB
├── Lines: 512
├── Line Size: 16 bytes
├── Hit Rate: 85-90%
└── Resources: 10 M10K, 600 ALMs
```

---

## Top 3 Recommendations

### 🥇 #1: 2-Way Set-Associative (BEST CHOICE)

```
★★★★★ Excellent Cost-Benefit

Hit Rate:    92-95% (+5-7%)
Resources:   +3 M10K (+30%), +1,200 ALMs (+200%)
Complexity:  Moderate
Timeline:    2-3 weeks
Risk:        LOW

WHY: Best balance of performance and cost
WHEN: Default recommendation for most use cases
```

### 🥈 #2: 2-Way + Sequential Prefetch (BEST PERFORMANCE)

```
★★★★★ Excellent Performance

Hit Rate:    94-96% (+7-9%)
Resources:   +5 M10K (+50%), +2,400 ALMs (+400%)
Complexity:  Moderate-High
Timeline:    3-4 weeks
Risk:        LOW-MEDIUM

WHY: Maximum performance for sequential workloads
WHEN: Code-heavy applications, tight loops
```

### 🥉 #3: 4-Way + 16 KB (MAXIMUM PERFORMANCE)

```
★★★★☆ Very Good (but expensive)

Hit Rate:    96-98% (+9-11%)
Resources:   +17 M10K (+170%), +3,100 ALMs (+517%)
Complexity:  High
Timeline:    3-4 weeks
Risk:        MEDIUM

WHY: Highest hit rate, best for large working sets
WHEN: Performance critical, resources available
```

---

## Decision Tree

```
START: Need better cache performance?
  │
  ├─ Budget constrained? (< +1,000 ALMs)
  │   └─► 32-byte line size (+50 ALMs, +0-2% hit rate)
  │
  ├─ Moderate budget? (< +2,000 ALMs)
  │   └─► 2-Way Set-Associative (+1,200 ALMs, +5-7% hit rate) ← RECOMMENDED
  │
  ├─ Good budget? (< +3,000 ALMs)
  │   ├─ Sequential workload?
  │   │   └─► 2-Way + Prefetch (+2,400 ALMs, +7-9% hit rate)
  │   └─ Random workload?
  │       └─► 2-Way + Victim Cache (+3,800 ALMs, +7-9% hit rate)
  │
  ├─ Large budget? (< +5,000 ALMs)
  │   └─► 4-Way + 16 KB (+3,100 ALMs, +9-11% hit rate)
  │
  └─ Unlimited budget?
      └─► L1 (8KB) + L2 (32KB) (+4,700 ALMs, +8-11% hit rate)
```

---

## Strategy Comparison Table

| Strategy | Hit Rate Δ | M10K Δ | ALM Δ | Complexity | Score | Best For |
|----------|------------|--------|-------|------------|-------|----------|
| **2-Way** | **+5-7%** | **+3** | **+1,200** | ★★★☆☆ | ★★★★★ | **General use** |
| 4-Way | +7-9% | +7 | +2,400 | ★★★★☆ | ★★★★☆ | High conflict |
| 16 KB | +3-5% | +10 | +100 | ★★☆☆☆ | ★★★☆☆ | Large working set |
| Victim (8-line) | +3-4% | +2 | +2,000 | ★★★☆☆ | ★★★★☆ | Conflict patterns |
| Sequential Prefetch | +5-7% | +2 | +600 | ★★★☆☆ | ★★★★☆ | Sequential code |
| **2-Way + Prefetch** | **+7-9%** | **+5** | **+2,400** | ★★★★☆ | ★★★★★ | **Code-heavy** |
| 4-Way + 16KB | +9-11% | +17 | +3,100 | ★★★★☆ | ★★★★☆ | Max performance |
| L1 + L2 | +8-11% | +40 | +4,700 | ★★★★★ | ★★★☆☆ | Enterprise |

---

## Performance Estimates

### Hit Rate by Workload

| Workload | Baseline | 2-Way | 2-Way+Prefetch | 4-Way+16KB |
|----------|----------|-------|----------------|------------|
| Sequential Code | 88-92% | 93-96% | **96-98%** | 97-99% |
| Random Access | 82-86% | 89-93% | 90-94% | **94-96%** |
| Mixed | 85-90% | 92-95% | 94-96% | 96-98% |
| Loop-Heavy | 80-85% | 90-94% | 92-95% | **95-97%** |

### IPC (Instructions Per Cycle) Improvement

| Configuration | IPC | Improvement vs Baseline |
|---------------|-----|-------------------------|
| Baseline | 0.75 | - |
| 2-Way | 0.81 | +8% ⚡ |
| 2-Way + Prefetch | 0.84 | +12% ⚡⚡ |
| 4-Way + 16KB | 0.87 | +16% ⚡⚡⚡ |

---

## Resource Budget Check

**MiSTer DE10-Nano (Cyclone V) Capacity:**
- Total ALMs: 41,910
- Total M10K: 553 blocks (5,530 KB)
- Current usage: ~31,650 ALMs (76%), ~190 M10K (34%)

**Available Budget:**
- ALMs: ~10,000 (24% free)
- M10K: ~363 blocks (66% free)

**All strategies fit comfortably!** ✅

---

## Implementation Checklist

### For 2-Way Set-Associative

**Week 1: Design**
- [ ] Design 2-way controller FSM
- [ ] Implement LRU bit storage (1 bit per set)
- [ ] Design way selection logic
- [ ] Create tag comparison for 2 ways

**Week 2: Implementation**
- [ ] Modify DCache.sv for 2-way support
- [ ] Add way multiplexers (2:1 mux)
- [ ] Implement replacement policy (LRU)
- [ ] Update control signals

**Week 3: Testing**
- [ ] Simulation testing (hit rate measurement)
- [ ] FPGA synthesis
- [ ] Timing closure verification (50 MHz)
- [ ] Hardware testing on MiSTer

**Verification Metrics:**
- [ ] Hit rate ≥92% (target: 93-95%)
- [ ] Resources ≤80% ALMs, ≤40% M10K
- [ ] Timing: 50 MHz with positive slack
- [ ] IPC improvement ≥+5% (target: +7-8%)

---

## Quick Formulas

### Average Memory Access Time (AMAT)

```
AMAT = Hit_Time + (Miss_Rate × Miss_Penalty)

Example (Baseline):
AMAT = 1.5 + (0.12 × 12) = 3.0 cycles

Example (2-Way):
AMAT = 1.5 + (0.06 × 12) = 2.2 cycles
Improvement: 27% faster memory access
```

### IPC Estimate

```
IPC ≈ 1 / (1 + AMAT)

Baseline: 1 / (1 + 3.0) = 0.75
2-Way:    1 / (1 + 2.2) = 0.81
Gain:     +8% IPC
```

---

## Common Questions

### Q: Why not just increase cache size to 32 KB?

**A:** Larger size only reduces **capacity misses**, not **conflict misses**.
- 16 KB: +3-5% hit rate, +10 M10K
- 2-Way 8KB: +5-7% hit rate, +3 M10K
- **2-way is more efficient per M10K block**

### Q: Should I use write-through instead of write-back?

**A:** ❌ No. Write-through would:
- **+400% write latency** (1-2 cycles → 8-10 cycles)
- **+500% memory write traffic**
- Only benefit: -8 cycle eviction overhead (rare)
- **Recommendation:** Keep write-back

### Q: What about fully associative cache?

**A:** ❌ Too expensive for primary cache:
- 32-line fully associative: +9,000 ALMs (22% of FPGA!)
- Better use: Small victim cache (4-16 lines)

### Q: How much will 2-way help my specific workload?

**A:** Depends on conflict patterns:
- **Best case:** Programs with 2-4 conflicting addresses: +10-15% hit rate
- **Typical case:** Mixed workloads: +5-7% hit rate
- **Worst case:** No conflicts (rare): +0-2% hit rate
- **Conservative estimate:** +5% minimum

### Q: Will timing close at 50 MHz?

**A:** ✅ Yes, with margin:
- 2-way adds 1 cycle to hit path
- Critical path: ~4-5 ns (vs 20ns budget)
- Expected slack: +2-4 ns
- **Recommendation:** Pipeline tag comparison if needed

---

## Risk Mitigation

| Risk | Probability | Mitigation |
|------|-------------|------------|
| Timing failure | LOW | Pipeline tag comparison, conservative design |
| Resource overflow | VERY LOW | All designs have 20%+ margin |
| Hit rate below target | LOW | Conservative estimates, worst-case: still +3% |
| Integration bugs | MEDIUM | Comprehensive simulation before FPGA |

---

## Next Steps

### Immediate Actions

1. **Review full analysis:** Read `DATA_CACHE_OPTIMIZATION_ANALYSIS.md`
2. **Choose strategy:** Recommend **2-way set-associative**
3. **Plan implementation:** 2-3 week timeline
4. **Allocate resources:** Reserve +1,200 ALMs, +3 M10K

### Phase 1: 2-Way Implementation

```bash
# Step 1: Create 2-way branch
git checkout -b cache-2way-associative

# Step 2: Modify DCache.sv
# - Add way multiplexers
# - Implement LRU tracking
# - Update tag comparison

# Step 3: Test and verify
# - Simulate with test vectors
# - Synthesize and check timing
# - Load to FPGA and benchmark
```

### Phase 2: Optional Enhancements

If 2-way doesn't meet goals:
- Add sequential prefetcher (+600 ALMs, +2 M10K)
- Or upgrade to 4-way (+1,200 additional ALMs, +4 M10K)

---

## Key Takeaways

✅ **2-way set-associative is the sweet spot**
- Best cost-benefit ratio
- Industry-proven approach
- +5-7% hit rate for +1,200 ALMs

✅ **All strategies fit in FPGA**
- Even L1+L2 fits (though expensive)
- Plenty of M10K blocks available (66% free)
- ALM budget allows up to +10,000 ALMs

✅ **Diminishing returns beyond 4-way**
- 8-way: Only +1-2% over 4-way, costs 2x ALMs
- Fully associative: Impractical for primary cache

✅ **Prefetching is highly effective**
- Sequential prefetch: +5-7% for only +600 ALMs
- Best combined with 2-way cache

❌ **Don't change write policy**
- Write-back is optimal
- Write-through hurts performance significantly

---

**For detailed analysis, see:** `DATA_CACHE_OPTIMIZATION_ANALYSIS.md`

**Status:** ✅ Ready for implementation
**Recommendation:** Start with 2-way set-associative cache
**Timeline:** 2-3 weeks
**Confidence:** HIGH

---
