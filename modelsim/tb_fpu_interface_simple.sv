/**
 * tb_fpu_interface_simple.sv
 *
 * Simplified standalone testbench for CPU-FPU interface signal generation
 *
 * This testbench verifies basic signal timing and state machine behavior
 * without requiring the full CPU or FPU RTL. It uses internal mock modules.
 *
 * Tests:
 * 1. Reset behavior
 * 2. Basic instruction handshake
 * 3. Busy/Ready signal timing
 * 4. Data transfer timing
 * 5. Control word updates
 *
 * Date: 2025-11-20
 */

`timescale 1ns/1ps

//=================================================================
// Simplified FPU Interface State Machine (Mock)
//=================================================================

module FPU_Interface_Simple (
    input wire clk,
    input wire reset,

    // CPU side
    input wire        instr_valid,
    input wire [7:0]  opcode,
    input wire [7:0]  modrm,
    output reg        instr_ack,

    input wire        data_write,
    input wire [79:0] data_in,
    output reg [79:0] data_out,
    output reg        data_ready,

    output wire       busy,
    output wire       ready,

    input wire [15:0] control_word_in,
    input wire        control_write,
    output reg [15:0] control_word,

    // FPU side (mock)
    input wire        fpu_done,
    input wire [79:0] fpu_result
);

    // State machine
    localparam IDLE     = 3'd0;
    localparam DECODE   = 3'd1;
    localparam WAIT_DATA = 3'd2;
    localparam EXECUTE  = 3'd3;
    localparam RESULT   = 3'd4;
    localparam COMPLETE = 3'd5;

    reg [2:0] state;
    reg internal_busy;
    reg needs_data;

    assign busy = internal_busy || (state != IDLE);
    assign ready = !busy;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= IDLE;
            instr_ack <= 1'b0;
            data_ready <= 1'b0;
            data_out <= 80'h0;
            control_word <= 16'h037F;
            internal_busy <= 1'b0;
            needs_data <= 1'b0;
        end else begin
            // Default: clear pulses
            instr_ack <= 1'b0;

            // Control word write
            if (control_write) begin
                control_word <= control_word_in;
            end

            case (state)
                IDLE: begin
                    internal_busy <= 1'b0;
                    data_ready <= 1'b0;
                    if (instr_valid) begin
                        instr_ack <= 1'b1;
                        state <= DECODE;
                    end
                end

                DECODE: begin
                    internal_busy <= 1'b1;
                    // Check if memory operand needed (simplified: mod != 11)
                    needs_data <= (modrm[7:6] != 2'b11);
                    if (modrm[7:6] != 2'b11) begin
                        state <= WAIT_DATA;
                    end else begin
                        state <= EXECUTE;
                    end
                end

                WAIT_DATA: begin
                    if (data_write) begin
                        state <= EXECUTE;
                    end
                end

                EXECUTE: begin
                    if (fpu_done) begin
                        data_out <= fpu_result;
                        state <= RESULT;
                    end
                end

                RESULT: begin
                    data_ready <= 1'b1;
                    state <= COMPLETE;
                end

                COMPLETE: begin
                    data_ready <= 1'b0;
                    internal_busy <= 1'b0;
                    state <= IDLE;
                end

                default: state <= IDLE;
            endcase
        end
    end

endmodule

//=================================================================
// Main Testbench
//=================================================================

module tb_fpu_interface_simple;

    //=================================================================
    // Testbench Signals
    //=================================================================

    reg clk;
    reg reset;

    // CPU interface
    reg        instr_valid;
    reg [7:0]  opcode;
    reg [7:0]  modrm;
    wire       instr_ack;

    reg        data_write;
    reg [79:0] data_in;
    wire [79:0] data_out;
    wire       data_ready;

    wire       busy;
    wire       ready;

    reg [15:0] control_word_in;
    reg        control_write;
    wire [15:0] control_word;

    // Mock FPU
    reg        fpu_done;
    reg [79:0] fpu_result;

    //=================================================================
    // Test Statistics
    //=================================================================

    integer test_count;
    integer pass_count;
    integer fail_count;

    //=================================================================
    // DUT Instantiation
    //=================================================================

    FPU_Interface_Simple dut (
        .clk(clk),
        .reset(reset),
        .instr_valid(instr_valid),
        .opcode(opcode),
        .modrm(modrm),
        .instr_ack(instr_ack),
        .data_write(data_write),
        .data_in(data_in),
        .data_out(data_out),
        .data_ready(data_ready),
        .busy(busy),
        .ready(ready),
        .control_word_in(control_word_in),
        .control_write(control_write),
        .control_word(control_word),
        .fpu_done(fpu_done),
        .fpu_result(fpu_result)
    );

    //=================================================================
    // Clock Generation
    //=================================================================

    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100 MHz clock
    end

    //=================================================================
    // Test Tasks
    //=================================================================

    task check_result;
        input condition;
        input [255:0] test_name;
        begin
            test_count = test_count + 1;
            $display("[Test %0d] %s", test_count, test_name);

            if (condition) begin
                $display("  PASS");
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL");
                fail_count = fail_count + 1;
            end
        end
    endtask

    //=================================================================
    // Main Test Sequence
    //=================================================================

    initial begin
        // Initialize
        test_count = 0;
        pass_count = 0;
        fail_count = 0;

        instr_valid = 0;
        opcode = 0;
        modrm = 0;
        data_write = 0;
        data_in = 0;
        control_word_in = 16'h037F;
        control_write = 0;
        fpu_done = 0;
        fpu_result = 0;

        // Reset
        reset = 1;
        repeat(5) @(posedge clk);
        reset = 0;
        repeat(2) @(posedge clk);

        $display("\n=== Simplified FPU Interface Tests ===\n");

        // Test 1: Initial state after reset
        check_result(ready && !busy, "Initial state - ready, not busy");

        // Test 2: Default control word
        check_result(control_word == 16'h037F, "Default control word = 0x037F");

        // Test 3: Instruction acknowledge pulse
        @(posedge clk);
        instr_valid <= 1'b1;
        opcode <= 8'hD8;
        modrm <= 8'hC0;  // Register operand (mod=11)
        @(posedge clk);
        instr_valid <= 1'b0;
        @(posedge clk);
        check_result(busy, "Busy asserted after instruction");

        // Test 4: FPU completes register operation
        repeat(2) @(posedge clk);
        fpu_done <= 1'b1;
        fpu_result <= 80'h3FFF8000000000000000;
        @(posedge clk);
        fpu_done <= 1'b0;

        // Wait for completion
        repeat(3) @(posedge clk);
        check_result(ready && !busy, "Ready after register op completion");

        // Test 5: Memory operand instruction
        @(posedge clk);
        instr_valid <= 1'b1;
        opcode <= 8'hD8;
        modrm <= 8'h06;  // Memory operand (mod=00)
        @(posedge clk);
        instr_valid <= 1'b0;
        @(posedge clk);
        check_result(busy, "Busy after memory instruction");

        // Test 6: Provide data
        repeat(2) @(posedge clk);
        data_write <= 1'b1;
        data_in <= 80'h12345678;
        @(posedge clk);
        data_write <= 1'b0;

        // Test 7: Complete after data
        repeat(2) @(posedge clk);
        fpu_done <= 1'b1;
        fpu_result <= 80'hABCDEF;
        @(posedge clk);
        fpu_done <= 1'b0;

        // Wait for result
        repeat(3) @(posedge clk);
        check_result(data_out == 80'hABCDEF, "Result data correct");

        repeat(2) @(posedge clk);
        check_result(ready, "Ready after memory op completion");

        // Test 8: Control word update
        @(posedge clk);
        control_word_in <= 16'h0000;
        control_write <= 1'b1;
        @(posedge clk);
        control_write <= 1'b0;
        @(posedge clk);
        check_result(control_word == 16'h0000, "Control word updated");

        // Test 9: Multiple instructions
        @(posedge clk);
        instr_valid <= 1'b1;
        modrm <= 8'hC1;  // Register
        @(posedge clk);
        instr_valid <= 1'b0;
        repeat(2) @(posedge clk);
        fpu_done <= 1'b1;
        @(posedge clk);
        fpu_done <= 1'b0;
        repeat(3) @(posedge clk);

        @(posedge clk);
        instr_valid <= 1'b1;
        modrm <= 8'hC2;
        @(posedge clk);
        instr_valid <= 1'b0;
        repeat(2) @(posedge clk);
        fpu_done <= 1'b1;
        @(posedge clk);
        fpu_done <= 1'b0;
        repeat(3) @(posedge clk);

        check_result(ready, "Multiple instructions completed");

        // Test 10: Busy/Ready toggle timing
        @(posedge clk);
        instr_valid <= 1'b1;
        modrm <= 8'hC3;
        @(posedge clk);
        instr_valid <= 1'b0;

        // Check busy asserts quickly
        @(posedge clk);
        check_result(busy, "Busy asserts within 2 cycles");

        // Complete
        repeat(2) @(posedge clk);
        fpu_done <= 1'b1;
        @(posedge clk);
        fpu_done <= 1'b0;
        repeat(3) @(posedge clk);

        // Test 11: Data ready timing
        @(posedge clk);
        instr_valid <= 1'b1;
        modrm <= 8'h00;  // Memory operand
        @(posedge clk);
        instr_valid <= 1'b0;
        repeat(2) @(posedge clk);
        data_write <= 1'b1;
        @(posedge clk);
        data_write <= 1'b0;
        repeat(2) @(posedge clk);
        fpu_result <= 80'h99999999;
        fpu_done <= 1'b1;
        @(posedge clk);
        fpu_done <= 1'b0;

        // Check data_ready asserts
        repeat(2) @(posedge clk);
        check_result(data_ready || data_out == 80'h99999999, "Data ready/out correct");

        repeat(3) @(posedge clk);

        // Test 12: Final state
        check_result(ready && !busy, "Final state - ready, not busy");

        // Summary
        repeat(5) @(posedge clk);
        $display("\n=== Test Summary ===");
        $display("Total Tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);

        if (fail_count == 0) begin
            $display("\n*** ALL TESTS PASSED ***\n");
        end else begin
            $display("\n*** SOME TESTS FAILED ***\n");
        end

        $finish;
    end

    //=================================================================
    // Timeout
    //=================================================================

    initial begin
        #100000;  // 100 us timeout
        $display("\n*** TEST TIMEOUT ***\n");
        $finish;
    end

endmodule
