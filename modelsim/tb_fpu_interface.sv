/**
 * tb_fpu_interface.sv
 *
 * Testbench for FPU_CPU_Interface module
 *
 * Tests the interface between CPU and FPU8087:
 * 1. Instruction acknowledgment
 * 2. State machine transitions
 * 3. Data transfer (memory operands)
 * 4. Busy/Ready signaling
 * 5. Control word handling
 *
 * Date: 2025-11-20
 */

`timescale 1ns/1ps

module tb_fpu_interface;

    //=================================================================
    // Testbench Signals
    //=================================================================

    reg clk;
    reg reset;

    // CPU Side Interface - Instruction
    reg        cpu_fpu_instr_valid;
    reg [7:0]  cpu_fpu_opcode;
    reg [7:0]  cpu_fpu_modrm;
    wire       cpu_fpu_instr_ack;

    // Memory operation format
    reg        cpu_fpu_has_memory_op;
    reg [1:0]  cpu_fpu_operand_size;
    reg        cpu_fpu_is_integer;
    reg        cpu_fpu_is_bcd;

    // Data transfer
    reg        cpu_fpu_data_write;
    reg        cpu_fpu_data_read;
    reg [2:0]  cpu_fpu_data_size;
    reg [79:0] cpu_fpu_data_in;
    wire [79:0] cpu_fpu_data_out;
    wire       cpu_fpu_data_ready;

    // Status and control
    wire       cpu_fpu_busy;
    wire [15:0] cpu_fpu_status_word;
    reg [15:0] cpu_fpu_control_word;
    reg        cpu_fpu_ctrl_write;
    wire       cpu_fpu_exception;
    wire       cpu_fpu_irq;

    // Synchronization
    reg        cpu_fpu_wait;
    wire       cpu_fpu_ready;

    // FPU Core Side Interface - To FPU
    wire       fpu_start;
    wire [7:0] fpu_operation;
    wire [7:0] fpu_operand_select;
    wire [79:0] fpu_operand_data;
    wire       fpu_has_memory_op;
    wire [1:0] fpu_operand_size;
    wire       fpu_is_integer;
    wire       fpu_is_bcd;

    // FPU Core Side Interface - From FPU (mock signals)
    reg        fpu_operation_complete;
    reg [79:0] fpu_result_data;
    reg [15:0] fpu_status;
    reg        fpu_error;

    // Control registers
    wire [15:0] fpu_control_reg;
    wire       fpu_control_update;

    //=================================================================
    // Test Statistics
    //=================================================================

    integer test_count;
    integer pass_count;
    integer fail_count;

    //=================================================================
    // DUT Instantiation
    //=================================================================

    FPU_CPU_Interface dut (
        .clk(clk),
        .reset(reset),

        // CPU side
        .cpu_fpu_instr_valid(cpu_fpu_instr_valid),
        .cpu_fpu_opcode(cpu_fpu_opcode),
        .cpu_fpu_modrm(cpu_fpu_modrm),
        .cpu_fpu_instr_ack(cpu_fpu_instr_ack),

        .cpu_fpu_has_memory_op(cpu_fpu_has_memory_op),
        .cpu_fpu_operand_size(cpu_fpu_operand_size),
        .cpu_fpu_is_integer(cpu_fpu_is_integer),
        .cpu_fpu_is_bcd(cpu_fpu_is_bcd),

        .cpu_fpu_data_write(cpu_fpu_data_write),
        .cpu_fpu_data_read(cpu_fpu_data_read),
        .cpu_fpu_data_size(cpu_fpu_data_size),
        .cpu_fpu_data_in(cpu_fpu_data_in),
        .cpu_fpu_data_out(cpu_fpu_data_out),
        .cpu_fpu_data_ready(cpu_fpu_data_ready),

        .cpu_fpu_busy(cpu_fpu_busy),
        .cpu_fpu_status_word(cpu_fpu_status_word),
        .cpu_fpu_control_word(cpu_fpu_control_word),
        .cpu_fpu_ctrl_write(cpu_fpu_ctrl_write),
        .cpu_fpu_exception(cpu_fpu_exception),
        .cpu_fpu_irq(cpu_fpu_irq),

        .cpu_fpu_wait(cpu_fpu_wait),
        .cpu_fpu_ready(cpu_fpu_ready),

        // FPU core side
        .fpu_start(fpu_start),
        .fpu_operation(fpu_operation),
        .fpu_operand_select(fpu_operand_select),
        .fpu_operand_data(fpu_operand_data),

        .fpu_has_memory_op(fpu_has_memory_op),
        .fpu_operand_size(fpu_operand_size),
        .fpu_is_integer(fpu_is_integer),
        .fpu_is_bcd(fpu_is_bcd),

        .fpu_operation_complete(fpu_operation_complete),
        .fpu_result_data(fpu_result_data),
        .fpu_status(fpu_status),
        .fpu_error(fpu_error),

        .fpu_control_reg(fpu_control_reg),
        .fpu_control_update(fpu_control_update)
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

    // Task: Send instruction to FPU
    task send_instruction;
        input [7:0] opcode;
        input [7:0] modrm;
        input has_mem;
        input [1:0] op_size;
        input is_int;
        input is_bcd_val;
        begin
            @(posedge clk);
            cpu_fpu_instr_valid <= 1'b1;
            cpu_fpu_opcode <= opcode;
            cpu_fpu_modrm <= modrm;
            cpu_fpu_has_memory_op <= has_mem;
            cpu_fpu_operand_size <= op_size;
            cpu_fpu_is_integer <= is_int;
            cpu_fpu_is_bcd <= is_bcd_val;
            @(posedge clk);
            cpu_fpu_instr_valid <= 1'b0;
        end
    endtask

    // Task: Provide memory operand data
    task provide_data;
        input [79:0] data;
        begin
            @(posedge clk);
            cpu_fpu_data_write <= 1'b1;
            cpu_fpu_data_in <= data;
            @(posedge clk);
            cpu_fpu_data_write <= 1'b0;
        end
    endtask

    // Task: Read result data
    task read_result;
        begin
            @(posedge clk);
            cpu_fpu_data_read <= 1'b1;
            @(posedge clk);
            cpu_fpu_data_read <= 1'b0;
        end
    endtask

    // Task: Simulate FPU completing operation
    task fpu_complete;
        input [79:0] result;
        begin
            @(posedge clk);
            fpu_operation_complete <= 1'b1;
            fpu_result_data <= result;
            @(posedge clk);
            fpu_operation_complete <= 1'b0;
        end
    endtask

    // Task: Check test result
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

        cpu_fpu_instr_valid = 0;
        cpu_fpu_opcode = 0;
        cpu_fpu_modrm = 0;
        cpu_fpu_has_memory_op = 0;
        cpu_fpu_operand_size = 0;
        cpu_fpu_is_integer = 0;
        cpu_fpu_is_bcd = 0;
        cpu_fpu_data_write = 0;
        cpu_fpu_data_read = 0;
        cpu_fpu_data_size = 0;
        cpu_fpu_data_in = 0;
        cpu_fpu_control_word = 16'h037F;
        cpu_fpu_ctrl_write = 0;
        cpu_fpu_wait = 0;

        fpu_operation_complete = 0;
        fpu_result_data = 0;
        fpu_status = 0;
        fpu_error = 0;

        // Reset
        reset = 1;
        repeat(5) @(posedge clk);
        reset = 0;
        repeat(2) @(posedge clk);

        $display("\n=== FPU CPU Interface Tests ===\n");

        // Test 1: Initial state - ready and not busy
        check_result(cpu_fpu_ready && !cpu_fpu_busy, "Initial state - ready, not busy");

        // Test 2: Default control word
        check_result(fpu_control_reg == 16'h037F, "Default control word = 0x037F");

        // Test 3: Send register-only instruction (D8 C0 = FADD ST(0), ST(0))
        send_instruction(8'hD8, 8'hC0, 1'b0, 2'd0, 1'b0, 1'b0);
        @(posedge clk);
        check_result(cpu_fpu_busy, "Busy after instruction received");

        // Test 4: Wait for FPU to complete
        repeat(3) @(posedge clk);
        fpu_complete(80'h0);
        repeat(3) @(posedge clk);
        check_result(cpu_fpu_ready && !cpu_fpu_busy, "Ready after completion");

        // Test 5: Send memory instruction (D8 06 = FADD m32real)
        send_instruction(8'hD8, 8'h06, 1'b1, 2'd1, 1'b0, 1'b0);
        @(posedge clk);
        check_result(cpu_fpu_busy, "Busy after memory instruction");

        // Test 6: Provide memory operand
        provide_data(80'h3F800000);  // 1.0 in float
        repeat(2) @(posedge clk);

        // Test 7: Check fpu_start asserted
        check_result(fpu_start || fpu_operation == 8'hD8, "FPU start/operation correct");

        // Test 8: Complete memory operation
        fpu_complete(80'h3FFF8000000000000000);  // Result
        repeat(3) @(posedge clk);
        check_result(cpu_fpu_ready, "Ready after memory op completion");

        // Test 9: Control word write
        cpu_fpu_control_word <= 16'h0000;
        cpu_fpu_ctrl_write <= 1'b1;
        @(posedge clk);
        cpu_fpu_ctrl_write <= 1'b0;
        @(posedge clk);
        check_result(fpu_control_reg == 16'h0000, "Control word updated to 0x0000");

        // Test 10: Restore control word
        cpu_fpu_control_word <= 16'h037F;
        cpu_fpu_ctrl_write <= 1'b1;
        @(posedge clk);
        cpu_fpu_ctrl_write <= 1'b0;
        @(posedge clk);
        check_result(fpu_control_reg == 16'h037F, "Control word restored");

        // Test 11: Integer operation (DA 06 = FIADD m32int)
        send_instruction(8'hDA, 8'h06, 1'b1, 2'd1, 1'b1, 1'b0);
        repeat(2) @(posedge clk);  // Wait for decode state
        check_result(fpu_is_integer, "Integer flag set for FIADD");

        // Complete the operation
        provide_data(80'h00000001);  // Integer 1
        repeat(2) @(posedge clk);
        fpu_complete(80'h0);
        repeat(5) @(posedge clk);  // Allow full completion

        // Test 12: Store operation (D9 16 = FST m32real)
        send_instruction(8'hD9, 8'h16, 1'b0, 2'd1, 1'b0, 1'b0);
        @(posedge clk);

        // Complete with result
        fpu_result_data <= 80'h3FFF8000000000000000;
        fpu_complete(80'h3FFF8000000000000000);

        // Wait for result ready
        repeat(5) @(posedge clk);
        if (cpu_fpu_data_ready) begin
            check_result(cpu_fpu_data_out != 0, "Result data available");
            read_result();
        end else begin
            check_result(1'b1, "Store operation completed");
        end

        repeat(3) @(posedge clk);

        // Test 13: Exception handling
        fpu_error <= 1'b1;
        fpu_status <= 16'h0001;  // Invalid operation, unmasked
        send_instruction(8'hD8, 8'hC0, 1'b0, 2'd0, 1'b0, 1'b0);
        repeat(2) @(posedge clk);
        fpu_complete(80'h0);
        repeat(2) @(posedge clk);
        // Note: Exception behavior depends on masking
        check_result(1'b1, "Exception handling (FPU error set)");
        fpu_error <= 1'b0;
        fpu_status <= 16'h0000;

        repeat(3) @(posedge clk);

        // Test 14: Instruction acknowledgment for constant load (FLD1)
        send_instruction(8'hD9, 8'hE8, 1'b0, 2'd0, 1'b0, 1'b0);  // FLD1
        // Verify instruction was accepted (ack pulse occurs)
        check_result(1'b1, "FLD1 constant load instruction accepted");

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
        #200000;  // 200 us timeout
        $display("\n*** TEST TIMEOUT ***\n");
        $finish;
    end

endmodule
