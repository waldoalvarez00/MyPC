// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// This file is part of MyPC.
//
// MyPC is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// MyPC is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with MyPC.  If not, see <http://www.gnu.org/licenses/>.

/*
 * Harvard Cache System - Complete I-cache + D-cache + Arbiter
 *
 * This module integrates the complete Harvard architecture cache system:
 * - Separate instruction cache (I-cache)
 * - Separate data cache (D-cache)
 * - Harvard arbiter for memory access
 *
 * This provides a drop-in replacement for the single unified cache,
 * maintaining the same interface to the CPU Core.
 *
 * Performance Improvements vs. Unified Cache:
 * - Eliminates I/D serialization bottleneck
 * - Allows parallel cache hits (I-fetch + D-access in same cycle)
 * - Better memory bandwidth utilization
 * - Expected 30-50% performance improvement on realistic workloads
 *
 * Resource Utilization:
 * - Approximately 2x the BlockRAM of single cache (16 KB total)
 * - Modest increase in logic for separate controllers
 * - Estimated +3,000 LUTs vs. unified cache
 * - Still fits comfortably in MiSTer DE10-Nano (Cyclone V)
 *
 * Interface:
 * - Same CPU-facing interface as original MemArbiter
 * - Transparent replacement - no CPU modifications needed
 * - Memory-facing interface unchanged
 */

`default_nettype none
module HarvardCacheSystem(
    input logic clk,
    input logic reset,
    input logic cache_enabled,

    // CPU instruction bus
    input logic [19:1] instr_m_addr,
    output logic [15:0] instr_m_data_in,
    input logic instr_m_access,
    output logic instr_m_ack,

    // CPU data bus
    input logic [19:1] data_m_addr,
    output logic [15:0] data_m_data_in,
    input logic [15:0] data_m_data_out,
    input logic data_m_access,
    output logic data_m_ack,
    input logic data_m_wr_en,
    input logic [1:0] data_m_bytesel,

    // Memory system interface
    output logic [19:1] mem_m_addr,
    input logic [15:0] mem_m_data_in,
    output logic [15:0] mem_m_data_out,
    output logic mem_m_access,
    input logic mem_m_ack,
    output logic mem_m_wr_en,
    output logic [1:0] mem_m_bytesel
);

// Cache parameters
parameter ICACHE_LINES = 512;  // 8 KB I-cache
parameter DCACHE_LINES = 512;  // 8 KB D-cache

// Interconnect signals between caches and arbiter
logic [19:1] icache_mem_addr;
logic [15:0] icache_mem_data_in;
logic icache_mem_access;
logic icache_mem_ack;

logic [19:1] dcache_mem_addr;
logic [15:0] dcache_mem_data_in;
logic [15:0] dcache_mem_data_out;
logic dcache_mem_access;
logic dcache_mem_ack;
logic dcache_mem_wr_en;
logic [1:0] dcache_mem_bytesel;

// D-cache victim writeback port (non-blocking)
logic [19:1] dcache_vwb_addr;
logic [15:0] dcache_vwb_data_out;
logic dcache_vwb_access;
logic dcache_vwb_ack;
logic dcache_vwb_wr_en;
logic [1:0] dcache_vwb_bytesel;

// Coherence interface between D-cache and I-cache
logic        coh_wr_valid;
logic [19:1] coh_wr_addr;
logic [15:0] coh_wr_data;
logic [1:0]  coh_wr_bytesel;
logic        coh_probe_valid;
logic [19:1] coh_probe_addr;
logic        coh_probe_present;

// Instruction Cache - 2-way set-associative with coherence support
ICache2Way #(
    .sets(ICACHE_LINES / 2)  // 256 sets × 2 ways = 512 lines = 8 KB
) icache (
    .clk(clk),
    .reset(reset),
    .enabled(cache_enabled),

    // CPU-facing interface
    .c_addr(instr_m_addr),
    .c_data_in(instr_m_data_in),
    .c_access(instr_m_access),
    .c_ack(instr_m_ack),

    // Memory-facing interface (to arbiter)
    .m_addr(icache_mem_addr),
    .m_data_in(icache_mem_data_in),
    .m_access(icache_mem_access),
    .m_ack(icache_mem_ack),

    // Coherence interface from D-cache
    .coh_wr_valid(coh_wr_valid),
    .coh_wr_addr(coh_wr_addr),
    .coh_wr_data(coh_wr_data),
    .coh_wr_bytesel(coh_wr_bytesel),
    .coh_probe_valid(coh_probe_valid),
    .coh_probe_addr(coh_probe_addr),
    .coh_probe_present(coh_probe_present),

    // Invalidation interface (tie off for now)
    .inval_valid(1'b0),
    .inval_addr(19'b0)
);

// Data Cache - 2-way set-associative with non-blocking victim writeback
DCache2Way #(
    .sets(DCACHE_LINES / 2)  // 256 sets × 2 ways = 512 lines = 8 KB
) dcache (
    .clk(clk),
    .reset(reset),
    .enabled(cache_enabled),

    // CPU-facing interface
    .c_addr(data_m_addr),
    .c_data_in(data_m_data_in),
    .c_data_out(data_m_data_out),
    .c_access(data_m_access),
    .c_ack(data_m_ack),
    .c_wr_en(data_m_wr_en),
    .c_bytesel(data_m_bytesel),

    // Memory-facing interface - main port (fills and flushes)
    .m_addr(dcache_mem_addr),
    .m_data_in(dcache_mem_data_in),
    .m_data_out(dcache_mem_data_out),
    .m_access(dcache_mem_access),
    .m_ack(dcache_mem_ack),
    .m_wr_en(dcache_mem_wr_en),
    .m_bytesel(dcache_mem_bytesel),

    // Memory-facing interface - victim writeback port (non-blocking)
    .vwb_addr(dcache_vwb_addr),
    .vwb_data_out(dcache_vwb_data_out),
    .vwb_access(dcache_vwb_access),
    .vwb_ack(dcache_vwb_ack),
    .vwb_wr_en(dcache_vwb_wr_en),
    .vwb_bytesel(dcache_vwb_bytesel),

    // Coherence interface to I-cache (for self-modifying code support)
    .coh_wr_valid(coh_wr_valid),
    .coh_wr_addr(coh_wr_addr),
    .coh_wr_data(coh_wr_data),
    .coh_wr_bytesel(coh_wr_bytesel),
    .coh_probe_valid(coh_probe_valid),
    .coh_probe_addr(coh_probe_addr),
    .coh_probe_present(coh_probe_present)
);

// Harvard 3-Way Arbiter - supports non-blocking victim writeback
HarvardArbiter3Way harvard_arbiter (
    .clk(clk),
    .reset(reset),

    // I-cache interface
    .icache_m_addr(icache_mem_addr),
    .icache_m_data_in(icache_mem_data_in),
    .icache_m_access(icache_mem_access),
    .icache_m_ack(icache_mem_ack),

    // D-cache main interface (fills and flushes)
    .dcache_m_addr(dcache_mem_addr),
    .dcache_m_data_in(dcache_mem_data_in),
    .dcache_m_data_out(dcache_mem_data_out),
    .dcache_m_access(dcache_mem_access),
    .dcache_m_ack(dcache_mem_ack),
    .dcache_m_wr_en(dcache_mem_wr_en),
    .dcache_m_bytesel(dcache_mem_bytesel),

    // D-cache victim writeback interface (non-blocking)
    .dcache_vwb_addr(dcache_vwb_addr),
    .dcache_vwb_data_out(dcache_vwb_data_out),
    .dcache_vwb_access(dcache_vwb_access),
    .dcache_vwb_ack(dcache_vwb_ack),
    .dcache_vwb_wr_en(dcache_vwb_wr_en),
    .dcache_vwb_bytesel(dcache_vwb_bytesel),

    // Memory interface
    .mem_m_addr(mem_m_addr),
    .mem_m_data_in(mem_m_data_in),
    .mem_m_data_out(mem_m_data_out),
    .mem_m_access(mem_m_access),
    .mem_m_ack(mem_m_ack),
    .mem_m_wr_en(mem_m_wr_en),
    .mem_m_bytesel(mem_m_bytesel)
);

// Performance monitoring (optional - can be removed for production)
`ifdef PERFORMANCE_COUNTERS
    integer icache_accesses, icache_hits, icache_misses;
    integer dcache_accesses, dcache_hits, dcache_misses;

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            icache_accesses <= 0;
            icache_hits <= 0;
            icache_misses <= 0;
            dcache_accesses <= 0;
            dcache_hits <= 0;
            dcache_misses <= 0;
        end else begin
            if (instr_m_access) begin
                icache_accesses <= icache_accesses + 1;
                if (instr_m_ack)
                    icache_hits <= icache_hits + 1;
                else if (icache_mem_access)
                    icache_misses <= icache_misses + 1;
            end

            if (data_m_access) begin
                dcache_accesses <= dcache_accesses + 1;
                if (data_m_ack)
                    dcache_hits <= dcache_hits + 1;
                else if (dcache_mem_access)
                    dcache_misses <= dcache_misses + 1;
            end
        end
    end
`endif

endmodule
`default_nettype wire
