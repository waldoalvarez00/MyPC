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
 * Instruction Cache (I-Cache) - Read-Only Harvard Architecture
 *
 * This module implements a direct-mapped instruction cache optimized for
 * read-only instruction fetches. Part of a Harvard architecture with
 * separate I-cache and D-cache for improved performance.
 *
 * Features:
 * - Direct-mapped cache organization
 * - 512 cache lines (configurable)
 * - 8-word (16-byte) cache line size
 * - Read-only (no write support needed for instructions)
 * - Simple fill logic (no flush needed)
 * - Optimized for sequential instruction fetch patterns
 *
 * Cache Organization:
 * - Total size: 512 lines * 8 words * 2 bytes = 8 KB
 * - Address breakdown: [tag | index | offset]
 *   - Tag: Upper bits for line identification
 *   - Index: Middle bits select cache line (9 bits for 512 lines)
 *   - Offset: Lower 3 bits select word within line
 *
 * Performance:
 * - Hit latency: 1-2 cycles
 * - Miss latency: 8-16 cycles (memory fetch)
 * - No write overhead (instructions are read-only)
 */

`default_nettype none
module ICache(
    input logic clk,
    input logic reset,
    input logic enabled,

    // Frontend - CPU instruction fetch interface
    input logic [19:1] c_addr,
    output logic [15:0] c_data_in,
    input logic c_access,
    output logic c_ack,

    // Backend - Memory system interface
    output logic [19:1] m_addr,
    input logic [15:0] m_data_in,
    output logic m_access,
    input logic m_ack
);

parameter lines = 512;

localparam line_size = 8;
localparam index_bits = $clog2(lines);
localparam tag_bits = 19 - 3 - index_bits;
localparam index_start = 4;
localparam index_end = 4 + index_bits - 1;
localparam tag_start = 4 + index_bits;

// Internal registers
reg [19:1] c_m_addr;
reg [2:0] line_idx;
wire [19:tag_start] tag;
reg [7:0] line_valid;
reg busy;
wire valid;
wire write_line = m_ack;
reg [index_end-1:0] line_address;
reg [19:1] latched_address, fetch_address;
reg updating;
reg accessing;

// Hit/miss logic
wire tags_match = tag == fetch_address[19:tag_start];
wire filling_current = fetch_address[19:index_start] == latched_address[19:index_start];
wire hit = accessing && ((valid && tags_match) ||
    (busy && filling_current && line_valid[fetch_address[3:1]]));

// Output logic
wire [15:0] c_q;
reg c_ack_reg;
assign c_data_in = enabled ? (c_ack ? c_q : 16'b0) : m_data_in;
assign c_ack = enabled ? c_ack_reg : m_ack;

// Memory interface - simplified for read-only
assign m_addr = enabled ? c_m_addr : c_addr;
assign m_access = enabled ? busy & ~m_ack : c_access;

// Cache miss triggers fill
wire do_fill = updating && ~hit && !busy;

wire write_tag = do_fill;
wire write_valid = write_tag | (line_idx == 3'b111 && m_ack);

// Tag RAM - stores tag bits for each cache line
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

// Valid RAM - tracks which cache lines contain valid data
DPRam #(.words(lines),
        .width(1))
      ValidRam(.clk(clk),
               .addr_a(c_addr[index_end:index_start]),
               .wr_en_a(1'b0),
               .wdata_a(1'b0),
               .q_a(valid),
               .addr_b(latched_address[index_end:index_start]),
               .wr_en_b(write_valid),
               .wdata_b(line_idx == 3'b111),
               .q_b());

// Line RAM - stores actual instruction data
BlockRam #(.words(lines * line_size))
         LineRAM(.clk(clk),
                 .addr_a(c_addr[index_end:1]),
                 .wr_en_a(1'b0),  // Read-only from CPU side
                 .wdata_a(16'b0),
                 .be_a(2'b11),
                 .q_a(c_q),
                 .addr_b(line_address),
                 .wr_en_b(write_line),
                 .wdata_b(m_data_in),
                 .q_b(),
                 .be_b(2'b11));

// Fill line task - simpler than Cache.sv (no flush needed)
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
        accessing <= 1'b0;
        c_ack_reg <= 1'b0;
    end else begin
        accessing <= c_access;
        // Register ACK to align with BlockRam read latency
        // Clear immediately when access goes low
        if (!c_access)
            c_ack_reg <= 1'b0;
        else
            c_ack_reg <= accessing & hit;
    end
end

// Line address calculation
always_comb begin
    line_address = {latched_address[index_end:index_start], c_m_addr[3:1]};
end

// Address latching
always_ff @(posedge clk) begin
    if (!busy)
        latched_address <= c_addr;
    fetch_address <= c_addr;
end

// Update state machine
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        updating <= 1'b0;
    end else begin
        if (enabled && !busy && c_access)
            updating <= 1'b1;
        else if (updating && !busy)
            updating <= 1'b0;
    end
end

// Fill state machine
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        line_idx <= 3'b0;
        line_valid <= 8'b0;
    end else if (enabled && m_ack) begin
        c_m_addr <= {c_m_addr[19:4], c_m_addr[3:1] + 1'b1};
        line_idx <= line_idx + 1'b1;
        line_valid[c_m_addr[3:1]] <= 1'b1;
        if (line_idx == 3'b111) begin
            busy <= 1'b0;
        end
    end else if (enabled && do_fill)
        fill_line();
end

endmodule
`default_nettype wire
