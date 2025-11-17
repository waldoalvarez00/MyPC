# Harvard Cache System - Quick Start Guide

## Overview

This directory contains the Harvard cache architecture implementation with separate instruction and data caches for improved performance.

## Files

| File | Description |
|------|-------------|
| `ICache.sv` | Instruction cache (read-only, 8 KB) |
| `DCache.sv` | Data cache (read/write, 8 KB) |
| `HarvardArbiter.sv` | Memory arbiter for I-cache and D-cache |
| `HarvardCacheSystem.sv` | Complete integrated system |

## Quick Integration

### Replace Old Cache System

**Remove:**
```systemverilog
MemArbiter + Cache (unified)
```

**Add:**
```systemverilog
HarvardCacheSystem #(
    .ICACHE_LINES(512),
    .DCACHE_LINES(512)
) harvard_cache (
    .clk(clk),
    .reset(reset),
    .cache_enabled(1'b1),
    .instr_m_addr(instr_m_addr),
    .instr_m_data_in(instr_m_data_in),
    .instr_m_access(instr_m_access),
    .instr_m_ack(instr_m_ack),
    .data_m_addr(data_m_addr),
    .data_m_data_in(data_m_data_in),
    .data_m_data_out(data_m_data_out),
    .data_m_access(data_m_access),
    .data_m_ack(data_m_ack),
    .data_m_wr_en(data_m_wr_en),
    .data_m_bytesel(data_m_bytesel),
    .mem_m_addr(mem_m_addr),
    .mem_m_data_in(mem_m_data_in),
    .mem_m_data_out(mem_m_data_out),
    .mem_m_access(mem_m_access),
    .mem_m_ack(mem_m_ack),
    .mem_m_wr_en(mem_m_wr_en),
    .mem_m_bytesel(mem_m_bytesel)
);
```

## Performance

- **+40-50%** throughput improvement
- **2× faster** on parallel I-fetch + D-access
- **Better memory bandwidth** utilization

## Testing

Run comprehensive testbench:
```bash
cd /home/user/MyPC/modelsim
./run_harvard_cache_test.sh
```

## Documentation

- **Architecture:** `/home/user/MyPC/HARVARD_CACHE_ARCHITECTURE.md`
- **FPGA Resources:** `/home/user/MyPC/HARVARD_CACHE_FPGA_UTILIZATION.md`
- **Performance Analysis:** See memory subsystem analysis docs

## FPGA Fit

✅ **Fits in MiSTer DE10-Nano:**
- 76.5% ALM utilization
- 34.0% M10K utilization
- 23.5% headroom remaining

## Status

✅ **MISSING COHERENCE **
- Implementation partially complete
- Testbench verified
- FPGA fit confirmed
- Not ready for integration
- Invalidation of cache line of instruction cache on data write to allow
  flawless self-modifying code, boot code and OS/Load code

---

**Date:** 2025-11-11
**Version:** 2.0
