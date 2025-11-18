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
 * D-Cache Frontend Arbiter
 *
 * Multiplexes CPU, DMA, and FPU requests to the D-cache frontend.
 * Ensures cache coherency by routing all data memory accesses through the cache.
 *
 * Key Features:
 * - 3-port arbitration (CPU, DMA, FPU)
 * - Priority-based arbitration (DMA > FPU > CPU)
 * - Registered outputs for glitch-free operation
 * - Minimal latency (1 cycle arbitration)
 * - Solves cache coherency issues (no stale data)
 *
 * Priority Rationale:
 * 1. DMA (Highest) - Critical for I/O transfers (floppy, disk)
 * 2. FPU (Medium) - Minimize floating-point operation stalls
 * 3. CPU (Lowest) - Most tolerant to delays (prefetch, pipeline)
 *
 * Coherency Guarantee:
 * - DMA writes update cache → CPU sees new data
 * - CPU writes stay in cache → FPU reads from cache
 * - FPU writes update cache → CPU sees new data
 * - All memory accesses go through single cache → no stale data
 */

`default_nettype none
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

//=============================================================================
// State Machine for Arbitration
//=============================================================================

typedef enum logic [1:0] {
    IDLE = 2'b00,
    SERVING_DMA = 2'b01,
    SERVING_FPU = 2'b10,
    SERVING_CPU = 2'b11
} state_t;

state_t state, next_state;

// Registered selection for output routing
logic serving_dma, serving_fpu, serving_cpu;

//=============================================================================
// State Machine - Sequential Logic
//=============================================================================

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        state <= IDLE;
        serving_dma <= 1'b0;
        serving_fpu <= 1'b0;
        serving_cpu <= 1'b0;
    end else begin
        state <= next_state;

        // Update serving flags based on CURRENT or NEXT state
        // This ensures:
        //  1. Serving flag goes HIGH immediately when entering SERVING state
        //  2. Serving flag stays HIGH for 1 cycle after leaving SERVING state
        // This prevents immediate re-entry while avoiding stuck conditions
        serving_dma <= (state == SERVING_DMA) || (next_state == SERVING_DMA);
        serving_fpu <= (state == SERVING_FPU) || (next_state == SERVING_FPU);
        serving_cpu <= (state == SERVING_CPU) || (next_state == SERVING_CPU);
    end
end

//=============================================================================
// State Machine - Combinational Next State Logic
//=============================================================================

// Priority: DMA > FPU > CPU
// Note: Transitions to IDLE after ACK, then waits one cycle before accepting
// new requests. This prevents re-entering the same SERVING state before the
// requestor has dropped their access signal.
always_comb begin
    next_state = state;

    case (state)
        IDLE: begin
            // Only transition if NOT just completing a request
            // (serving flags are still high for one cycle after transitioning to IDLE)
            if (!serving_dma && !serving_fpu && !serving_cpu) begin
                // Check requests in priority order
                if (dma_access)
                    next_state = SERVING_DMA;
                else if (fpu_access)
                    next_state = SERVING_FPU;
                else if (cpu_access)
                    next_state = SERVING_CPU;
            end
        end

        SERVING_DMA: begin
            // Stay serving DMA until cache acknowledges
            if (cache_ack)
                next_state = IDLE;
        end

        SERVING_FPU: begin
            // Stay serving FPU until cache acknowledges
            if (cache_ack)
                next_state = IDLE;
        end

        SERVING_CPU: begin
            // Stay serving CPU until cache acknowledges
            if (cache_ack)
                next_state = IDLE;
        end

        default: next_state = IDLE;
    endcase
end

//=============================================================================
// Output Multiplexing - Route Winner's Signals to Cache
//=============================================================================

// Address multiplexing
assign cache_addr = serving_dma ? dma_addr :
                    serving_fpu ? fpu_addr :
                    serving_cpu ? cpu_addr :
                    19'b0;

// Data output multiplexing
assign cache_data_out = serving_dma ? dma_data_out :
                        serving_fpu ? fpu_data_out :
                        serving_cpu ? cpu_data_out :
                        16'b0;

// Write enable multiplexing
assign cache_wr_en = serving_dma ? dma_wr_en :
                     serving_fpu ? fpu_wr_en :
                     serving_cpu ? cpu_wr_en :
                     1'b0;

// Byte select multiplexing
assign cache_bytesel = serving_dma ? dma_bytesel :
                       serving_fpu ? fpu_bytesel :
                       serving_cpu ? cpu_bytesel :
                       2'b11;

// Access signal - assert when serving any port
assign cache_access = (serving_dma && dma_access) ||
                      (serving_fpu && fpu_access) ||
                      (serving_cpu && cpu_access);

//=============================================================================
// ACK Generation - Route Cache ACK to Winner
//=============================================================================

// Registered ACK outputs for glitch-free operation
logic dma_ack_reg, fpu_ack_reg, cpu_ack_reg;

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        dma_ack_reg <= 1'b0;
        fpu_ack_reg <= 1'b0;
        cpu_ack_reg <= 1'b0;
    end else begin
        // Generate ACK pulse for the currently served port
        dma_ack_reg <= serving_dma && cache_ack;
        fpu_ack_reg <= serving_fpu && cache_ack;
        cpu_ack_reg <= serving_cpu && cache_ack;
    end
end

assign dma_ack = dma_ack_reg;
assign fpu_ack = fpu_ack_reg;
assign cpu_ack = cpu_ack_reg;

//=============================================================================
// Data Input Routing - Cache Data to Requestor
//=============================================================================

// Registered data inputs for glitch-free operation
logic [15:0] dma_data_in_reg, fpu_data_in_reg, cpu_data_in_reg;

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        dma_data_in_reg <= 16'b0;
        fpu_data_in_reg <= 16'b0;
        cpu_data_in_reg <= 16'b0;
    end else begin
        // Latch data when acknowledged
        if (serving_dma && cache_ack)
            dma_data_in_reg <= cache_data_in;
        if (serving_fpu && cache_ack)
            fpu_data_in_reg <= cache_data_in;
        if (serving_cpu && cache_ack)
            cpu_data_in_reg <= cache_data_in;
    end
end

assign dma_data_in = dma_data_in_reg;
assign fpu_data_in = fpu_data_in_reg;
assign cpu_data_in = cpu_data_in_reg;

//=============================================================================
// Debug Tracing (for simulation)
//=============================================================================

`ifndef SYNTHESIS
    always_ff @(posedge clk) begin
        if (!reset) begin
            // Monitor state transitions
            if (state != next_state) begin
                $display("[ARBITER] State transition: %0d → %0d", state, next_state);
            end

            // Monitor stuck conditions
            if (state != IDLE && !cache_ack && !cache_access) begin
                $display("[ARBITER] WARNING: In state %0d but cache_access=0 (serving_dma=%b serving_fpu=%b serving_cpu=%b)",
                         state, serving_dma, serving_fpu, serving_cpu);
            end

            // Trace grants and cache interface for debugging
            if (cache_access || cache_ack) begin
                $display("[ARBITER] cache_access=%b ack=%b wr_en=%b addr=%h data_out=%h bytesel=%b (serving_dma=%b serving_fpu=%b serving_cpu=%b)",
                         cache_access, cache_ack, cache_wr_en, cache_addr, cache_data_out, cache_bytesel,
                         serving_dma, serving_fpu, serving_cpu);
            end
            if (dma_access || dma_ack_reg) begin
                $display("[ARBITER] dma_access=%b ack=%b addr=%h data_out=%h bytesel=%b",
                         dma_access, dma_ack_reg, dma_addr, dma_data_out, dma_bytesel);
            end
        end
    end
`endif

//=============================================================================
// Assertions (for formal verification)
//=============================================================================

`ifdef FORMAL
    // Property: Only one port served at a time
    assert property (@(posedge clk) disable iff (reset)
        $onehot0({serving_dma, serving_fpu, serving_cpu}));

    // Property: No ACK without access
    assert property (@(posedge clk) disable iff (reset)
        dma_ack_reg |-> $past(dma_access && serving_dma));

    assert property (@(posedge clk) disable iff (reset)
        fpu_ack_reg |-> $past(fpu_access && serving_fpu));

    assert property (@(posedge clk) disable iff (reset)
        cpu_ack_reg |-> $past(cpu_access && serving_cpu));

    // Property: DMA priority over FPU
    assert property (@(posedge clk) disable iff (reset)
        (state == IDLE && dma_access && fpu_access) |=> (next_state == SERVING_DMA));

    // Property: DMA priority over CPU
    assert property (@(posedge clk) disable iff (reset)
        (state == IDLE && dma_access && cpu_access) |=> (next_state == SERVING_DMA));

    // Property: FPU priority over CPU
    assert property (@(posedge clk) disable iff (reset)
        (state == IDLE && !dma_access && fpu_access && cpu_access) |=> (next_state == SERVING_FPU));
`endif

endmodule
`default_nettype wire
