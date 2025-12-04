// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// Testbench for FPU I/O Registers Integration
//
// Tests:
// 1. FPU Control Word Register (write/read)
// 2. FPU Status Word Register (read)
// 3. I/O port addressing
// 4. Control word write pulse generation
// 5. Status word mirroring

`timescale 1ns / 1ps

module tb_fpu_io_registers;

    // Clock and reset
    reg clk;
    reg reset;

    // Control register signals
    reg fpu_control_cs;
    reg [15:0] control_data_in;
    reg control_wr_en;
    wire control_ack;
    wire [15:0] control_word_out;
    wire control_write_pulse;

    // Status register signals
    reg fpu_status_cs;
    reg [15:0] status_word_from_fpu;
    wire [15:0] status_data_out;
    wire status_ack;

    // Test tracking
    integer test_count;
    integer pass_count;
    integer fail_count;
    integer i;
    reg [15:0] test_values [0:3];

    // Instantiate FPU Control Word Register
    FPUControlRegister control_reg (
        .clk(clk),
        .reset(reset),
        .cs(fpu_control_cs),
        .data_m_data_in(control_data_in),
        .data_m_wr_en(control_wr_en),
        .data_m_ack(control_ack),
        .control_word_out(control_word_out),
        .control_write(control_write_pulse)
    );

    // Instantiate FPU Status Word Register
    FPUStatusRegister status_reg (
        .clk(clk),
        .reset(reset),
        .cs(fpu_status_cs),
        .status_word_in(status_word_from_fpu),
        .data_m_data_out(status_data_out),
        .data_m_ack(status_ack)
    );

    // Clock generation (50 MHz)
    initial begin
        clk = 0;
        forever #10 clk = ~clk;  // 20ns period = 50 MHz
    end

    // Test procedure
    initial begin
        $display("========================================");
        $display("FPU I/O Registers Integration Test");
        $display("========================================");

        // Initialize
        test_count = 0;
        pass_count = 0;
        fail_count = 0;

        reset = 1;
        fpu_control_cs = 0;
        control_data_in = 16'h0000;
        control_wr_en = 0;
        fpu_status_cs = 0;
        status_word_from_fpu = 16'h0000;

        // Release reset after a few cycles
        #100;
        reset = 0;
        #40;

        //======================================================================
        // TEST 1: Control Register Default Value
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: Control Register Default Value (0x037F)", test_count);

        if (control_word_out == 16'h037F) begin
            $display("  PASS: Default control word = 0x%04X", control_word_out);
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected 0x037F, got 0x%04X", control_word_out);
            fail_count = fail_count + 1;
        end

        //======================================================================
        // TEST 2: Write Control Word (0x0272 - Different precision/rounding)
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: Write Control Word (0x0272)", test_count);

        @(posedge clk);
        #5;
        fpu_control_cs = 1;
        control_data_in = 16'h0272;  // Modified control word
        control_wr_en = 1;

        @(posedge clk);
        #5;
        fpu_control_cs = 0;
        control_wr_en = 0;

        @(posedge clk);
        @(posedge clk);
        #5;

        if (control_word_out == 16'h0272) begin
            $display("  PASS: Control word written successfully = 0x%04X", control_word_out);
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected 0x0272, got 0x%04X", control_word_out);
            fail_count = fail_count + 1;
        end

        //======================================================================
        // TEST 3: Control Write Pulse Generation
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: Control Write Pulse Generation", test_count);

        @(posedge clk);
        #5;
        fpu_control_cs = 1;
        control_data_in = 16'h0100;
        control_wr_en = 1;

        @(posedge clk);
        #5;

        if (control_write_pulse == 1'b1) begin
            $display("  PASS: Write pulse generated during write");
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Write pulse not generated");
            fail_count = fail_count + 1;
        end

        fpu_control_cs = 0;
        control_wr_en = 0;

        @(posedge clk);
        #5;

        if (control_write_pulse == 1'b0) begin
            $display("  PASS: Write pulse cleared after one cycle");
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Write pulse should be one cycle only");
            fail_count = fail_count + 1;
        end

        //======================================================================
        // TEST 4: Control Register ACK Signal
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: Control Register ACK Signal", test_count);

        @(posedge clk);
        #5;
        fpu_control_cs = 1;

        @(posedge clk);
        #5;

        if (control_ack == 1'b1) begin
            $display("  PASS: ACK asserted when CS active");
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: ACK should be asserted");
            fail_count = fail_count + 1;
        end

        fpu_control_cs = 0;

        @(posedge clk);
        #5;

        if (control_ack == 1'b0) begin
            $display("  PASS: ACK deasserted when CS inactive");
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: ACK should be deasserted");
            fail_count = fail_count + 1;
        end

        //======================================================================
        // TEST 5: Status Register Read
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: Status Register Read", test_count);

        status_word_from_fpu = 16'hABCD;  // Simulated FPU status

        @(posedge clk);
        #5;
        fpu_status_cs = 1;

        @(posedge clk);
        #5;

        if (status_data_out == 16'hABCD) begin
            $display("  PASS: Status word mirrored correctly = 0x%04X", status_data_out);
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected 0xABCD, got 0x%04X", status_data_out);
            fail_count = fail_count + 1;
        end

        //======================================================================
        // TEST 6: Status Register ACK
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: Status Register ACK", test_count);

        if (status_ack == 1'b1) begin
            $display("  PASS: Status ACK asserted when CS active");
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Status ACK should be asserted");
            fail_count = fail_count + 1;
        end

        fpu_status_cs = 0;

        @(posedge clk);
        #5;

        if (status_ack == 1'b0) begin
            $display("  PASS: Status ACK deasserted when CS inactive");
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Status ACK should be deasserted");
            fail_count = fail_count + 1;
        end

        //======================================================================
        // TEST 7: Reset Behavior
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: Reset Behavior", test_count);

        // Write a custom control word
        @(posedge clk);
        #5;
        fpu_control_cs = 1;
        control_data_in = 16'hFFFF;
        control_wr_en = 1;

        @(posedge clk);
        #5;
        fpu_control_cs = 0;
        control_wr_en = 0;

        @(posedge clk);
        #5;

        // Apply reset
        reset = 1;
        @(posedge clk);
        @(posedge clk);
        #5;
        reset = 0;

        @(posedge clk);
        #5;

        if (control_word_out == 16'h037F) begin
            $display("  PASS: Control word reset to default 0x037F");
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected 0x037F after reset, got 0x%04X", control_word_out);
            fail_count = fail_count + 1;
        end

        //======================================================================
        // TEST 8: Multiple Status Updates
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: Multiple Status Updates", test_count);

        test_values[0] = 16'h0001;
        test_values[1] = 16'h8000;
        test_values[2] = 16'h5A5A;
        test_values[3] = 16'hA5A5;

        fpu_status_cs = 1;

        for (i = 0; i < 4; i = i + 1) begin
            status_word_from_fpu = test_values[i];
            @(posedge clk);
            #5;

            if (status_data_out == test_values[i]) begin
                $display("  PASS: Status update %0d: 0x%04X", i, status_data_out);
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL: Status update %0d: Expected 0x%04X, got 0x%04X",
                         i, test_values[i], status_data_out);
                fail_count = fail_count + 1;
            end
        end

        fpu_status_cs = 0;

        //======================================================================
        // Final Summary
        //======================================================================
        #100;

        $display("\n========================================");
        $display("Test Summary");
        $display("========================================");
        $display("Total Tests:  %0d", test_count);
        $display("Passed:       %0d", pass_count);
        $display("Failed:       %0d", fail_count);
        $display("Pass Rate:    %0d%%", (pass_count * 100) / test_count);
        $display("========================================");

        if (fail_count == 0) begin
            $display("✓ ALL TESTS PASSED!");
            $display("FPU I/O Registers integration validated successfully.");
        end else begin
            $display("✗ SOME TESTS FAILED");
            $display("Please review failures above.");
        end

        $display("\n");
        $finish;
    end

    // Timeout watchdog
    initial begin
        #100000;  // 100 microseconds timeout
        $display("\n*** ERROR: Test timeout! ***");
        $finish;
    end

endmodule
