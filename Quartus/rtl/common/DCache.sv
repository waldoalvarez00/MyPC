// Copyright 2025, Waldo Alvarez, https://pipflow.com
// Based on Cache.sv by Jamie Iles, 2018
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
 * Data Cache (D-Cache) - Read/Write Harvard Architecture
 *
 * This module implements a direct-mapped data cache optimized for
 * data load/store operations. Part of a Harvard architecture with
 * separate I-cache and D-cache for improved performance.
 *
 * Features:
 * - Direct-mapped cache organization
 * - 256 cache lines (configurable, reduced from 512 to save FPGA resources)
 * - 8-word (16-byte) cache line size
 * - Write-through with dirty bit tracking
 * - Automatic flush of dirty lines on replacement
 * - Byte-level write granularity
 *
 * Cache Organization:
 * - Total size: 256 lines * 8 words * 2 bytes = 4 KB
 * - Address breakdown: [tag | index | offset]
 *   - Tag: Upper bits for line identification
 *   - Index: Middle bits select cache line (8 bits for 256 lines)
 *   - Offset: Lower 3 bits select word within line
 *
 * Performance:
 * - Read hit latency: 1-2 cycles
 * - Write hit latency: 1-2 cycles
 * - Miss latency: 8-16 cycles (memory fetch)
 * - Dirty flush overhead: 8 cycles (when replacing dirty line)
 *
 * This is nearly identical to the original Cache.sv but specialized
 * for data access patterns and part of the Harvard architecture.
 */

`default_nettype none
module DCache(
    input logic clk,
    input logic reset,
    input logic enabled,

    // Frontend - CPU data access interface
    input logic [19:1] c_addr,
    output logic [15:0] c_data_in,
    input logic [15:0] c_data_out,
    input logic c_access,
    output logic c_ack,
    input logic c_wr_en,
    input logic [1:0] c_bytesel,

    // Backend - Memory system interface
    output logic [19:1] m_addr,
    input logic [15:0] m_data_in,
    output logic [15:0] m_data_out,
    output logic m_access,
    input logic m_ack,
    output logic m_wr_en,
    output logic [1:0] m_bytesel
);

parameter lines = 256;  // Reduced from 512 to save FPGA resources (4 KB cache)

localparam line_size = 8;
localparam index_bits = $clog2(lines);
localparam tag_bits = 19 - 3 - index_bits;
localparam index_start = 4;
localparam index_end = 4 + index_bits - 1;
localparam tag_start = 4 + index_bits;

// Internal registers
reg [19:1] c_m_addr;
reg [15:0] c_m_data_out;
reg [2:0] line_idx;
wire [19:tag_start] tag;
reg [7:0] line_valid;
reg busy;
reg flushing;
wire dirty;
wire write_line = m_ack && !flushing;
reg [index_end-1:0] line_address;
reg [19:1] latched_address, fetch_address;
reg updating;
reg accessing;

// Hit/miss logic
wire tags_match = tag == fetch_address[19:tag_start];
wire filling_current = fetch_address[19:index_start] == latched_address[19:index_start];
// Use c_addr for line_valid check (no RAM latency), fetch_address for tag check (1-cycle RAM latency)
wire hit = accessing && ((valid && tags_match) ||
    (busy && filling_current && line_valid[c_addr[3:1]]));

// Output logic
wire [15:0] c_q;
reg c_ack_reg;
assign c_data_in = enabled ? (c_ack ? c_q : 16'b0) : m_data_in;
assign c_ack = enabled ? c_ack_reg : m_ack;

// Memory interface
assign m_addr = enabled ? c_m_addr : c_addr;
assign m_wr_en = enabled ? flushing & ~m_ack : c_wr_en;
assign m_access = enabled ? busy & ~m_ack : c_access;
assign m_bytesel = enabled ? 2'b11 : c_bytesel;
assign m_data_out = enabled ? c_m_data_out : c_data_out;

// Flush and fill logic
wire do_flush = updating && ~hit && !busy && !flushing && dirty;
wire do_fill = updating && ~hit && !busy && !flushing && !dirty;

wire write_tag = do_fill;
wire valid;
wire write_valid = do_flush | write_tag | (~flushing && line_idx == 3'b111 && m_ack);

// Tag RAM
DPRam #(.words(lines),
        .width(tag_bits))
      TagRam(.clk(clk),
             .addr_a(c_addr[index_end:index_start]),
             .wr_en_a(1'b0),
             .wdata_a({tag_bits{1'b0}}),
             .q_a(tag),
             .addr_b(latched_address[index_end:index_start]),
             .wr_en_b(write_tag),
             .wdata_b(latched_address[19:tag_start]),
             .q_b());

// Valid RAM
DPRam #(.words(lines),
        .width(1))
      ValidRam(.clk(clk),
               .addr_a(c_addr[index_end:index_start]),
               .wr_en_a(1'b0),
               .wdata_a(1'b0),
               .q_a(valid),
               .addr_b(latched_address[index_end:index_start]),
               .wr_en_b(write_valid),
               .wdata_b(do_flush ? 1'b0 : (~flushing && line_idx == 3'b111)),
               .q_b());

// Dirty RAM
DPRam #(.words(lines),
        .width(1))
      DirtyRam(.clk(clk),
               .addr_a(c_addr[index_end:index_start]),
               .wr_en_a(c_ack & c_wr_en),
               .wdata_a(1'b1),
               .q_a(dirty),
               .addr_b(latched_address[index_end:index_start]),
               .wr_en_b(do_flush),
               .wdata_b(1'b0),
               .q_b());

// Line RAM
BlockRam #(.words(lines * line_size))
         LineRAM(.clk(clk),
                 .addr_a(c_addr[index_end:1]),
                 .wr_en_a(c_ack && c_wr_en && !flushing && hit),
                 .wdata_a(c_data_out),
                 .be_a(c_bytesel),
                 .q_a(c_q),
                 .addr_b(line_address),
                 .wr_en_b(write_line),
                 .wdata_b(m_data_in),
                 .q_b(c_m_data_out),
                 .be_b(2'b11));

// Flush task
task flush_line;
begin
    c_m_addr <= {tag, latched_address[index_end:index_start], 3'b0};
    busy <= 1'b1;
    flushing <= 1'b1;
end
endtask

// Fill task
task fill_line;
begin
    c_m_addr <= c_addr;
    busy <= 1'b1;
    line_valid <= 8'b0;
end
endtask

// Reset logic
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        busy <= 1'b0;
        flushing <= 1'b0;
        accessing <= 1'b0;
        c_ack_reg <= 1'b0;
    end else begin
        accessing <= c_access;
        // Register ACK to align with BlockRam read latency
        // Clear immediately when access goes low
        if (!c_access)
            c_ack_reg <= 1'b0;
        else
            c_ack_reg <= accessing & !flushing & hit;
    end
end

// Line address calculation
always_comb begin
    if (m_ack && flushing)
        line_address = {latched_address[index_end:index_start], c_m_addr[3:1] + 1'b1};
    else if (~hit && !flushing && !busy && dirty)
        line_address = {latched_address[index_end:index_start], 3'b0};
    else
        line_address = {latched_address[index_end:index_start], c_m_addr[3:1]};
end

// Address latching
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        latched_address <= 19'h0;
        fetch_address <= 19'h0;
    end else begin
        if (!busy && !flushing)
            latched_address <= c_addr;
        fetch_address <= c_addr;
    end
end

// Update state machine
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        updating <= 1'b0;
    end else begin
        if (enabled && !busy && !flushing && c_access)
            updating <= 1'b1;
        else if (updating && !busy && !flushing)
            updating <= 1'b0;
    end
end

// Fill/flush state machine
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        line_idx <= 3'b0;
        line_valid <= 8'b0;
    end else if (enabled && m_ack) begin
        c_m_addr <= {c_m_addr[19:4], c_m_addr[3:1] + 1'b1};
        line_idx <= line_idx + 1'b1;
        if (!flushing)
            line_valid[c_m_addr[3:1]] <= 1'b1;
        if (line_idx == 3'b111) begin
            busy <= 1'b0;
            if (flushing)
                flushing <= 1'b0;
        end
    end else if (enabled && do_flush)
        flush_line();
    else if (enabled && do_fill)
        fill_line();
end

endmodule
`default_nettype wire
