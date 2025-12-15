// Copyright Jamie Iles, 2017
// Copyright Waldo Alvarez, 2025, https://pipflow.com
//
// This file is part of s80x86.
//
// s80x86 is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// s80x86 is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with s80x86.  If not, see <http://www.gnu.org/licenses/>.



// Prefetcher
//
// This module is responsible for fetching bytes from the memory and pushing
// them into the instruction stream FIFO.  The CS is stored outside of the
// Prefetch unit and passed in to be combined with the internal IP which is
// wired out. This means that IP wrapping works correctly, and can be updated
// under external control. The fetching can be stalled when servicing
// a branch, updating the IP will flush the FIFO.

// SMC Detection implemented: Monitors data writes via coh_wr_* signals from cache
// and flushes FIFO if write address overlaps with prefetched instruction range.
// This enables Self-Modifying Code, Boot loader code, and OS-loaded code support.

`default_nettype none
module Prefetch(input logic clk,
                input logic reset,
					 
                // Address control.
                input logic [15:0] new_cs,
                input logic [15:0] new_ip,
                input logic load_new_ip,
					 
                // FIFO write port.
                output logic fifo_wr_en,
                output logic [7:0] fifo_wr_data,
                output logic fifo_reset,
                input logic fifo_full,
					 
                // Memory port.
                output logic mem_access,
                input logic mem_ack,
                output logic [19:1] mem_address,
                input logic [15:0] mem_data,
                // SMC Detection - Coherency from cache
                input logic        coh_wr_valid,     // Data write occurred
                input logic [19:1] coh_wr_addr,      // Write word address
                input logic [3:0]  fifo_count);      // FIFO occupancy (from external Fifo)

reg [15:0] next_fetch_address, fetch_address;
reg [15:0] next_cs, cs;
reg abort_cur;
reg [7:0] fetched_high_byte;
reg write_second;
reg [15:0] next_sequential_fetch;

wire should_write_second_byte = mem_ack && !abort_cur && !fetch_address[0] && !fifo_reset;

// verilator lint_off UNUSED
wire [15:0] next_address = mem_ack ? next_sequential_fetch : fetch_address;
// verilator lint_on UNUSED

wire [19:1] _mem_address = {cs, 3'b0} + {4'b0, next_address[15:1]};
wire _mem_access = !reset && !fifo_full && !mem_ack && !write_second && ~(~mem_access && load_new_ip);

reg mem_access2;
assign mem_access = mem_access2 & !mem_ack;

always_ff @(posedge clk) begin
mem_address <= _mem_address;
mem_access2 <= _mem_access;
end

assign fifo_wr_en = !abort_cur && !load_new_ip && (mem_ack || write_second);
assign fifo_reset = load_new_ip | (abort_cur & mem_ack) | smc_flush;


assign fifo_wr_data = mem_ack ?
    (fetch_address[0] ? mem_data[15:8] : mem_data[7:0]) : fetched_high_byte;
	 

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        abort_cur <= 1'b0;
    end else begin
        if (abort_cur && mem_ack)
            abort_cur <= 1'b0;
        else if (mem_access && load_new_ip)
            abort_cur <= 1'b1;
    end
end

always_ff @(posedge clk or posedge reset)
    if (reset)
        write_second <= 1'b0;
    else
        write_second <= should_write_second_byte;

always_ff @(posedge clk or posedge reset)
    if (reset) begin
        cs <= 16'hffff;
    end else begin
        if (abort_cur && mem_ack)
            cs <= next_cs;
        else if (load_new_ip && !mem_access)
            cs <= new_cs;
    end

always_ff @(posedge clk or posedge reset)
    if (reset)
        next_cs <= 16'hffff;
    else if (load_new_ip)
        next_cs <= new_cs;

always_ff @(posedge clk or posedge reset) begin
    if (reset)
        fetch_address <= 16'b0;
    else if (abort_cur && mem_ack)
        fetch_address <= next_fetch_address;
    else if (load_new_ip && !mem_access)
        fetch_address <= new_ip;
    else if (!abort_cur && !load_new_ip && (mem_ack || write_second))
        fetch_address <= fetch_address + 1'b1;
end

always_ff @(posedge clk or posedge reset) begin
    if (reset)
        next_fetch_address <= 16'b0;
    else if (load_new_ip)
        next_fetch_address <= new_ip;
end

always_ff @(posedge clk)
    if (mem_ack)
        fetched_high_byte <= mem_data[15:8];

always_ff @(posedge clk)
    next_sequential_fetch <= fetch_address + 1'b1;

// ============================================================================
// SMC Detection - Prefetch Range Tracking (REGISTERED for timing closure)
// ============================================================================

// Registered prefetch range for clean timing
reg [19:1] prefetch_start_addr;
reg [19:1] prefetch_end_addr;
reg        range_valid;
reg        range_wraps;

// Helper wires for range calculation
// fetch_address = NEXT byte to fetch, so first valid = fetch_address - fifo_count
wire [15:0] fifo_base_ip = fetch_address - {12'b0, fifo_count};

// Update range registers every cycle
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        prefetch_start_addr <= 19'b0;
        prefetch_end_addr   <= 19'b0;
        range_valid         <= 1'b0;
        range_wraps         <= 1'b0;
    end else begin
        range_valid <= (fifo_count != 4'd0) && !fifo_reset;
        range_wraps <= (fifo_base_ip > fetch_address);
        prefetch_start_addr <= {cs, 3'b0} + {4'b0, fifo_base_ip[15:1]};
        prefetch_end_addr   <= {cs, 3'b0} + {4'b0, fetch_address[15:1]};
    end
end

// Registered write detection (capture coh_wr_* for comparison)
reg        coh_wr_valid_r;
reg [19:1] coh_wr_addr_r;

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        coh_wr_valid_r <= 1'b0;
        coh_wr_addr_r  <= 19'b0;
    end else begin
        coh_wr_valid_r <= coh_wr_valid;
        coh_wr_addr_r  <= coh_wr_addr;
    end
end

// Compare registered write address against registered prefetch range
wire write_in_normal_range = (coh_wr_addr_r >= prefetch_start_addr) &&
                             (coh_wr_addr_r <= prefetch_end_addr);
wire write_in_wrapped_range = (coh_wr_addr_r >= prefetch_start_addr) ||
                              (coh_wr_addr_r <= prefetch_end_addr);

// Final SMC detection (1-cycle latency from write)
wire smc_flush = coh_wr_valid_r && range_valid &&
                 (range_wraps ? write_in_wrapped_range : write_in_normal_range);

endmodule
