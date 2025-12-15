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
 * Harvard Architecture 3-Way Memory Arbiter
 *
 * Enhanced arbiter supporting non-blocking cache architecture with separate
 * victim writeback stream.
 *
 * Key Features:
 * - 3-way arbitration: I-cache, D-cache main, D-cache victim writeback
 * - Priority-based scheduling for correctness and performance
 * - Non-blocking victim writebacks can proceed alongside cache operations
 * - Pipelined operation for improved throughput
 * - Registered outputs to prevent glitches
 * - Minimal latency overhead (1 cycle arbitration)
 *
 * Arbitration Policy:
 * 1. D-cache victim writeback has highest priority (frees victim buffer)
 * 2. D-cache main writes have second priority (flush operations)
 * 3. Round-robin between D-cache reads and I-cache reads
 * 4. Switch immediately when current operation completes
 *
 * Performance Benefits vs. 2-Way Arbiter:
 * - Victim writebacks don't block cache fills
 * - Better memory bandwidth utilization
 * - Eliminates blocking on dirty line evictions
 * - Expected additional 10-20% throughput improvement
 *
 * Interface:
 * - I-cache port: Read-only instruction fetch
 * - D-cache main port: Read/write for fills and flushes
 * - D-cache VWB port: Write-only for victim writeback
 * - Memory port: Unified memory interface
 */

`default_nettype none
module HarvardArbiter3Way(
    input logic clk,
    input logic reset,

    // I-cache interface (read-only)
    input logic [19:1] icache_m_addr,
    output logic [15:0] icache_m_data_in,
    input logic icache_m_access,
    output logic icache_m_ack,

    // D-cache main interface (read/write for fills and flushes)
    input logic [19:1] dcache_m_addr,
    output logic [15:0] dcache_m_data_in,
    input logic [15:0] dcache_m_data_out,
    input logic dcache_m_access,
    output logic dcache_m_ack,
    input logic dcache_m_wr_en,
    input logic [1:0] dcache_m_bytesel,

    // D-cache victim writeback interface (write-only, non-blocking)
    input logic [18:0] dcache_vwb_addr,  // Standard indexing
    input logic [15:0] dcache_vwb_data_out,
    input logic dcache_vwb_access,
    output logic dcache_vwb_ack,
    input logic dcache_vwb_wr_en,
    input logic [1:0] dcache_vwb_bytesel,

    // Memory interface
    output logic [19:1] mem_m_addr,
    input logic [15:0] mem_m_data_in,
    output logic [15:0] mem_m_data_out,
    output logic mem_m_access,
    input logic mem_m_ack,
    output logic mem_m_wr_en,
    output logic [1:0] mem_m_bytesel
);

// Arbitration state
typedef enum logic [1:0] {
    IDLE           = 2'b00,
    SERVING_ICACHE = 2'b01,
    SERVING_DCACHE = 2'b10,
    SERVING_VWB    = 2'b11
} arb_state_t;

arb_state_t state, next_state;
logic last_served_dcache;  // For round-robin fairness between ICache and DCache reads

// Registered outputs for glitch-free operation
logic icache_m_ack_reg;
logic dcache_m_ack_reg;
logic dcache_vwb_ack_reg;
logic [15:0] icache_m_data_in_reg;
logic [15:0] dcache_m_data_in_reg;

assign icache_m_ack = icache_m_ack_reg;
assign dcache_m_ack = dcache_m_ack_reg;
assign dcache_vwb_ack = dcache_vwb_ack_reg;
assign icache_m_data_in = icache_m_data_in_reg;
assign dcache_m_data_in = dcache_m_data_in_reg;

// Grant signals for output multiplexing
wire grant_icache = (state == SERVING_ICACHE);
wire grant_dcache = (state == SERVING_DCACHE);
wire grant_vwb    = (state == SERVING_VWB);

// Convert victim WB address from standard [18:0] to word addressing [19:1]
wire [19:1] dcache_vwb_addr_word;
assign dcache_vwb_addr_word[19:1] = dcache_vwb_addr[18:0];

// Output multiplexing - priority: VWB > DCache > ICache
assign mem_m_addr = grant_vwb    ? dcache_vwb_addr_word :
                    grant_dcache ? dcache_m_addr :
                                   icache_m_addr;

assign mem_m_data_out = grant_vwb    ? dcache_vwb_data_out :
                        grant_dcache ? dcache_m_data_out :
                                       16'b0;

assign mem_m_wr_en = grant_vwb    ? dcache_vwb_wr_en :
                     grant_dcache ? dcache_m_wr_en :
                                    1'b0;

assign mem_m_bytesel = grant_vwb    ? dcache_vwb_bytesel :
                       grant_dcache ? dcache_m_bytesel :
                                      2'b11;

assign mem_m_access = (grant_icache && icache_m_access) ||
                      (grant_dcache && dcache_m_access) ||
                      (grant_vwb && dcache_vwb_access);

// State machine - combinational next state logic
always_comb begin
    next_state = state;

    case (state)
        IDLE: begin
            // Priority: Victim WB > DCache writes > Round-robin reads
            if (dcache_vwb_access) begin
                // Victim writeback has highest priority (always write)
                next_state = SERVING_VWB;
            end else if (dcache_m_access && dcache_m_wr_en) begin
                // D-cache flush write has second priority
                next_state = SERVING_DCACHE;
            end else if (dcache_m_access && icache_m_access) begin
                // Both requesting reads - use round-robin
                if (last_served_dcache)
                    next_state = SERVING_ICACHE;
                else
                    next_state = SERVING_DCACHE;
            end else if (dcache_m_access) begin
                next_state = SERVING_DCACHE;
            end else if (icache_m_access) begin
                next_state = SERVING_ICACHE;
            end
        end

        SERVING_ICACHE: begin
            // Preempt for victim WB (highest priority)
            if (dcache_vwb_access) begin
                next_state = SERVING_VWB;
            end else if (!icache_m_access) begin
                // I-cache finished - check for other requests
                if (dcache_m_access)
                    next_state = SERVING_DCACHE;
                else
                    next_state = IDLE;
            end else if (mem_m_ack) begin
                // Completed current word - check for higher priority requests
                if (dcache_vwb_access)
                    next_state = SERVING_VWB;
                else if (dcache_m_access && dcache_m_wr_en)
                    next_state = SERVING_DCACHE;
                else if (dcache_m_access)
                    next_state = SERVING_DCACHE;
                else if (icache_m_access)
                    next_state = SERVING_ICACHE;  // Continue
                else
                    next_state = IDLE;
            end
        end

        SERVING_DCACHE: begin
            // Preempt for victim WB (highest priority)
            if (dcache_vwb_access && dcache_m_wr_en) begin
                // Don't preempt DCache writes (both are writes, avoid thrashing)
                next_state = SERVING_DCACHE;
            end else if (dcache_vwb_access && mem_m_ack) begin
                // Preempt DCache reads after current word completes
                next_state = SERVING_VWB;
            end else if (!dcache_m_access) begin
                // D-cache finished - check for other requests
                if (dcache_vwb_access)
                    next_state = SERVING_VWB;
                else if (icache_m_access)
                    next_state = SERVING_ICACHE;
                else
                    next_state = IDLE;
            end else if (mem_m_ack) begin
                // Completed current word - check for higher priority requests
                if (dcache_vwb_access)
                    next_state = SERVING_VWB;
                else if (icache_m_access && !dcache_m_wr_en)
                    next_state = SERVING_ICACHE;  // Switch to ICache if DCache is reading
                else if (dcache_m_access)
                    next_state = SERVING_DCACHE;  // Continue
                else
                    next_state = IDLE;
            end
        end

        SERVING_VWB: begin
            // Victim WB has highest priority - don't preempt
            if (!dcache_vwb_access) begin
                // VWB finished - check for other requests
                if (dcache_m_access)
                    next_state = SERVING_DCACHE;
                else if (icache_m_access)
                    next_state = SERVING_ICACHE;
                else
                    next_state = IDLE;
            end else if (mem_m_ack) begin
                // Completed current word - check for other requests
                if (dcache_vwb_access)
                    next_state = SERVING_VWB;  // Continue victim WB
                else if (dcache_m_access)
                    next_state = SERVING_DCACHE;
                else if (icache_m_access)
                    next_state = SERVING_ICACHE;
                else
                    next_state = IDLE;
            end
        end

        default: begin
            next_state = IDLE;
        end
    endcase
end

// State machine - sequential state update
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        state <= IDLE;
        last_served_dcache <= 1'b0;
    end else begin
        state <= next_state;

        // Track last served bus for round-robin fairness (ICache vs DCache reads)
        if (state == IDLE && next_state == SERVING_DCACHE && !dcache_m_wr_en)
            last_served_dcache <= 1'b1;
        else if (state == IDLE && next_state == SERVING_ICACHE)
            last_served_dcache <= 1'b0;
    end
end

// Output registers - update on acknowledge
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        icache_m_ack_reg <= 1'b0;
        dcache_m_ack_reg <= 1'b0;
        dcache_vwb_ack_reg <= 1'b0;
        icache_m_data_in_reg <= 16'b0;
        dcache_m_data_in_reg <= 16'b0;
    end else begin
        // Acknowledge signals - single cycle pulse
        icache_m_ack_reg <= grant_icache && mem_m_ack;
        dcache_m_ack_reg <= grant_dcache && mem_m_ack;
        dcache_vwb_ack_reg <= grant_vwb && mem_m_ack;

        // Data latching - hold data when acknowledged
        if (grant_icache && mem_m_ack)
            icache_m_data_in_reg <= mem_m_data_in;
        if (grant_dcache && mem_m_ack)
            dcache_m_data_in_reg <= mem_m_data_in;
        // VWB is write-only, no data latching needed
    end
end

// Debug output for simulation
`ifndef SYNTHESIS
    always_ff @(posedge clk) begin
        if (!reset && mem_m_access && mem_m_ack) begin
            if (grant_vwb) begin
                $display("[%0t][ARB] VWB_ACK addr=%h data=%h vwb_addr=%h", $time, mem_m_addr, mem_m_data_out, dcache_vwb_addr);
            end else if (grant_dcache && dcache_m_wr_en) begin
                $display("[%0t][ARB] DC_WR_ACK addr=%h data=%h dc_addr=%h", $time, mem_m_addr, mem_m_data_out, dcache_m_addr);
            end else if (grant_dcache) begin
                $display("[%0t][ARB] DC_RD_ACK addr=%h data=%h dc_addr=%h", $time, mem_m_addr, mem_m_data_in, dcache_m_addr);
            end else if (grant_icache) begin
                $display("[%0t][ARB] IC_RD_ACK addr=%h data=%h ic_addr=%h", $time, mem_m_addr, mem_m_data_in, icache_m_addr);
            end
        end
        // Debug: Trace state transitions
        if (!reset && state != next_state) begin
            $display("[%0t][ARB] STATE_CHANGE %0d->%0d (mem_access=%b mem_ack=%b)", $time, state, next_state, mem_m_access, mem_m_ack);
        end
    end
`endif

// Synthesis and simulation assertions
`ifdef FORMAL
    // Property: Only one bus served at a time
    assert property (@(posedge clk) disable iff (reset)
        $onehot0({grant_icache, grant_dcache, grant_vwb}));

    // Property: No ack without access
    assert property (@(posedge clk) disable iff (reset)
        icache_m_ack_reg |-> $past(icache_m_access));

    assert property (@(posedge clk) disable iff (reset)
        dcache_m_ack_reg |-> $past(dcache_m_access));

    assert property (@(posedge clk) disable iff (reset)
        dcache_vwb_ack_reg |-> $past(dcache_vwb_access));

    // Property: VWB is always write
    assert property (@(posedge clk) disable iff (reset)
        dcache_vwb_access |-> dcache_vwb_wr_en);
`endif

endmodule
`default_nettype wire
