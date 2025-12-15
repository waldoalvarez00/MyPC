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
 * Pipelined DMA/FPU/CPU Arbiter
 *
 * 3-port pipelined arbitration for DMA, FPU, and CPU cache memory access.
 * Based on PipelinedDMAArbiter with additional FPU support.
 *
 * 4-stage pipelined arbitration to hide arbitration latency:
 *   Stage 1: Request capture
 *   Stage 2: Arbitration decision (combinational)
 *   Stage 3: Winner registration
 *   Stage 4: Memory interface
 *
 * Priority Order:
 *   1. DMA (A-bus) - Highest priority (critical for floppy/disk transfers)
 *   2. FPU (C-bus) - Medium priority (FPU memory operands)
 *   3. CPU Cache (B-bus) - Lowest priority (normal CPU access)
 *
 * Key Features:
 *   - Back-to-back operations (no idle cycles)
 *   - Priority-based arbitration (DMA > FPU > CPU)
 *   - Registered outputs (glitch-free)
 *   - Compatible with existing PipelinedDMAArbiter interface
 *   - Supports FPU memory operand instructions (FADD [BX], FILD [SI])
 */

`default_nettype none
module PipelinedDMAFPUArbiter(
    input logic clk,
    input logic reset,

    // DMA bus (A-bus) - Highest priority
    input logic [19:1] a_m_addr,
    output logic [15:0] a_m_data_in,
    input logic [15:0] a_m_data_out,
    input logic a_m_access,
    output logic a_m_ack,
    input logic a_m_wr_en,
    input logic [1:0] a_m_bytesel,
    input logic ioa,

    // CPU Cache bus (B-bus) - Lowest priority
    input logic [19:1] b_m_addr,
    output logic [15:0] b_m_data_in,
    input logic [15:0] b_m_data_out,
    input logic b_m_access,
    output logic b_m_ack,
    input logic b_m_wr_en,
    input logic [1:0] b_m_bytesel,
    input logic iob,

    // FPU bus (C-bus) - Medium priority
    input logic [19:1] c_m_addr,
    output logic [15:0] c_m_data_in,
    input logic [15:0] c_m_data_out,
    input logic c_m_access,
    output logic c_m_ack,
    input logic c_m_wr_en,
    input logic [1:0] c_m_bytesel,

    // Output bus to next level arbiter
    output logic [19:1] q_m_addr,
    input logic [15:0] q_m_data_in,
    output logic [15:0] q_m_data_out,
    output logic q_m_access,
    input logic q_m_ack,
    output logic q_m_wr_en,
    output logic [1:0] q_m_bytesel,
    output logic ioq,
    output logic [1:0] q_grant  // 00=none, 01=A(DMA), 10=B(CPU), 11=C(FPU)
);

//=============================================================================
// Pipeline Stages
//=============================================================================

// Stage 1: Request capture
logic stage1_a_access;
logic stage1_b_access;
logic stage1_c_access;
logic [19:1] stage1_a_addr;
logic [19:1] stage1_b_addr;
logic [19:1] stage1_c_addr;
logic [15:0] stage1_a_data;
logic [15:0] stage1_b_data;
logic [15:0] stage1_c_data;
logic stage1_a_wr_en;
logic stage1_b_wr_en;
logic stage1_c_wr_en;
logic [1:0] stage1_a_bytesel;
logic [1:0] stage1_b_bytesel;
logic [1:0] stage1_c_bytesel;
logic stage1_ioa;
logic stage1_iob;

// Stage 2: Arbitration decision (combinational)
logic [1:0] stage2_grant;  // 00=none, 01=A, 10=B, 11=C
logic stage2_valid;        // 1 = winner selected

// Stage 3: Winner registration
logic [1:0] stage3_grant;
logic stage3_valid;
logic [19:1] stage3_addr;
logic [15:0] stage3_data_out;
logic stage3_wr_en;
logic [1:0] stage3_bytesel;
logic stage3_io;

// Stage 4: Memory access tracking
logic [1:0] stage4_grant;
logic stage4_valid;

//=============================================================================
// Stage 1: Request Capture
//=============================================================================

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        stage1_a_access <= 1'b0;
        stage1_b_access <= 1'b0;
        stage1_c_access <= 1'b0;
        stage1_a_addr <= 19'b0;
        stage1_b_addr <= 19'b0;
        stage1_c_addr <= 19'b0;
        stage1_a_data <= 16'b0;
        stage1_b_data <= 16'b0;
        stage1_c_data <= 16'b0;
        stage1_a_wr_en <= 1'b0;
        stage1_b_wr_en <= 1'b0;
        stage1_c_wr_en <= 1'b0;
        stage1_a_bytesel <= 2'b0;
        stage1_b_bytesel <= 2'b0;
        stage1_c_bytesel <= 2'b0;
        stage1_ioa <= 1'b0;
        stage1_iob <= 1'b0;
    end else begin
        // Capture new requests only if previous request completed or no valid request
        if (!stage4_valid || q_m_ack) begin
            stage1_a_access <= a_m_access;
            stage1_b_access <= b_m_access;
            stage1_c_access <= c_m_access;
            stage1_a_addr <= a_m_addr;
            stage1_b_addr <= b_m_addr;
            stage1_c_addr <= c_m_addr;
            stage1_a_data <= a_m_data_out;
            stage1_b_data <= b_m_data_out;
            stage1_c_data <= c_m_data_out;
            stage1_a_wr_en <= a_m_wr_en;
            stage1_b_wr_en <= b_m_wr_en;
            stage1_c_wr_en <= c_m_wr_en;
            stage1_a_bytesel <= a_m_bytesel;
            stage1_b_bytesel <= b_m_bytesel;
            stage1_c_bytesel <= c_m_bytesel;
            stage1_ioa <= ioa;
            stage1_iob <= iob;
        end
    end
end

//=============================================================================
// Stage 2: Arbitration Decision (Combinational)
//=============================================================================

// Priority: A-bus (DMA) > C-bus (FPU) > B-bus (CPU Cache)
always_comb begin
    if (stage1_a_access) begin
        // DMA has highest priority
        stage2_grant = 2'b01;  // Grant A
        stage2_valid = 1'b1;
    end else if (stage1_c_access) begin
        // FPU has medium priority
        stage2_grant = 2'b11;  // Grant C
        stage2_valid = 1'b1;
    end else if (stage1_b_access) begin
        // CPU Cache has lowest priority
        stage2_grant = 2'b10;  // Grant B
        stage2_valid = 1'b1;
    end else begin
        stage2_grant = 2'b00;  // No grant
        stage2_valid = 1'b0;
    end
end

//=============================================================================
// Stage 3: Winner Registration
//=============================================================================

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        stage3_grant <= 2'b00;
        stage3_valid <= 1'b0;
        stage3_addr <= 19'b0;
        stage3_data_out <= 16'b0;
        stage3_wr_en <= 1'b0;
        stage3_bytesel <= 2'b0;
        stage3_io <= 1'b0;
    end else begin
        // Advance pipeline if previous stage completed or no valid request
        if (!stage4_valid || q_m_ack) begin
            stage3_grant <= stage2_grant;
            stage3_valid <= stage2_valid;

            // Multiplex winner's signals
            case (stage2_grant)
                2'b01: begin  // A-bus (DMA)
                    stage3_addr <= stage1_a_addr;
                    stage3_data_out <= stage1_a_data;
                    stage3_wr_en <= stage1_a_wr_en;
                    stage3_bytesel <= stage1_a_bytesel;
                    stage3_io <= stage1_ioa;
                end
                2'b10: begin  // B-bus (CPU)
                    stage3_addr <= stage1_b_addr;
                    stage3_data_out <= stage1_b_data;
                    stage3_wr_en <= stage1_b_wr_en;
                    stage3_bytesel <= stage1_b_bytesel;
                    stage3_io <= stage1_iob;
                end
                2'b11: begin  // C-bus (FPU)
                    stage3_addr <= stage1_c_addr;
                    stage3_data_out <= stage1_c_data;
                    stage3_wr_en <= stage1_c_wr_en;
                    stage3_bytesel <= stage1_c_bytesel;
                    stage3_io <= 1'b0;  // FPU never accesses I/O
                end
                default: begin
                    stage3_addr <= 19'b0;
                    stage3_data_out <= 16'b0;
                    stage3_wr_en <= 1'b0;
                    stage3_bytesel <= 2'b0;
                    stage3_io <= 1'b0;
                end
            endcase
        end
    end
end

//=============================================================================
// Stage 4: Memory Interface
//=============================================================================

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        stage4_grant <= 2'b00;
        stage4_valid <= 1'b0;
    end else begin
        if (q_m_ack) begin
            // Request completed, mark invalid
            stage4_valid <= 1'b0;
        end else if (stage3_valid && (!stage4_valid || q_m_ack)) begin
            // New request entering stage 4
            stage4_grant <= stage3_grant;
            stage4_valid <= 1'b1;
        end
    end
end

//=============================================================================
// Output Assignments
//=============================================================================

// Memory interface outputs
assign q_m_addr = stage3_addr;
assign q_m_data_out = stage3_data_out;
assign q_m_wr_en = stage3_wr_en;
assign q_m_bytesel = stage3_bytesel;
assign ioq = stage3_io;
assign q_grant = stage3_grant;
assign q_m_access = stage4_valid && !q_m_ack;

// Registered acknowledge and data outputs
logic a_m_ack_reg;
logic b_m_ack_reg;
logic c_m_ack_reg;
logic [15:0] a_m_data_in_reg;
logic [15:0] b_m_data_in_reg;
logic [15:0] c_m_data_in_reg;

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        a_m_ack_reg <= 1'b0;
        b_m_ack_reg <= 1'b0;
        c_m_ack_reg <= 1'b0;
        a_m_data_in_reg <= 16'b0;
        b_m_data_in_reg <= 16'b0;
        c_m_data_in_reg <= 16'b0;
    end else begin
        // Generate acknowledge pulses
        a_m_ack_reg <= stage4_valid && (stage4_grant == 2'b01) && q_m_ack;
        b_m_ack_reg <= stage4_valid && (stage4_grant == 2'b10) && q_m_ack;
        c_m_ack_reg <= stage4_valid && (stage4_grant == 2'b11) && q_m_ack;

        // Latch data when acknowledged
        if (stage4_valid && (stage4_grant == 2'b01) && q_m_ack)
            a_m_data_in_reg <= q_m_data_in;
        if (stage4_valid && (stage4_grant == 2'b10) && q_m_ack)
            b_m_data_in_reg <= q_m_data_in;
        if (stage4_valid && (stage4_grant == 2'b11) && q_m_ack)
            c_m_data_in_reg <= q_m_data_in;
    end
end

assign a_m_ack = a_m_ack_reg;
assign b_m_ack = b_m_ack_reg;
assign c_m_ack = c_m_ack_reg;
assign a_m_data_in = a_m_data_in_reg;
assign b_m_data_in = b_m_data_in_reg;
assign c_m_data_in = c_m_data_in_reg;

//=============================================================================
// Performance Counters (optional, for debugging)
//=============================================================================

`ifdef PERFORMANCE_COUNTERS
    integer total_cycles;
    integer a_requests;
    integer b_requests;
    integer c_requests;
    integer a_acks;
    integer b_acks;
    integer c_acks;
    integer pipeline_stalls;

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            total_cycles <= 0;
            a_requests <= 0;
            b_requests <= 0;
            c_requests <= 0;
            a_acks <= 0;
            b_acks <= 0;
            c_acks <= 0;
            pipeline_stalls <= 0;
        end else begin
            total_cycles <= total_cycles + 1;

            if (a_m_access) a_requests <= a_requests + 1;
            if (b_m_access) b_requests <= b_requests + 1;
            if (c_m_access) c_requests <= c_requests + 1;
            if (a_m_ack_reg) a_acks <= a_acks + 1;
            if (b_m_ack_reg) b_acks <= b_acks + 1;
            if (c_m_ack_reg) c_acks <= c_acks + 1;

            // Stall = valid request but pipeline can't accept
            if ((stage1_a_access || stage1_b_access || stage1_c_access) &&
                stage4_valid && !q_m_ack)
                pipeline_stalls <= pipeline_stalls + 1;
        end
    end
`endif

//=============================================================================
// Assertions (for formal verification)
//=============================================================================

`ifdef FORMAL
    // Property: Only one bus acknowledged at a time
    assert property (@(posedge clk) disable iff (reset)
        $onehot0({a_m_ack_reg, b_m_ack_reg, c_m_ack_reg}));

    // Property: Ack implies previous access
    assert property (@(posedge clk) disable iff (reset)
        a_m_ack_reg |-> $past(stage4_valid && (stage4_grant == 2'b01)));

    assert property (@(posedge clk) disable iff (reset)
        b_m_ack_reg |-> $past(stage4_valid && (stage4_grant == 2'b10)));

    assert property (@(posedge clk) disable iff (reset)
        c_m_ack_reg |-> $past(stage4_valid && (stage4_grant == 2'b11)));

    // Property: DMA priority over FPU
    assert property (@(posedge clk) disable iff (reset)
        (stage1_a_access && stage1_c_access) |=> (stage3_grant == 2'b01));

    // Property: DMA priority over CPU
    assert property (@(posedge clk) disable iff (reset)
        (stage1_a_access && stage1_b_access) |=> (stage3_grant == 2'b01));

    // Property: FPU priority over CPU
    assert property (@(posedge clk) disable iff (reset)
        (stage1_c_access && stage1_b_access && !stage1_a_access)
        |=> (stage3_grant == 2'b11));
`endif

endmodule
`default_nettype wire
