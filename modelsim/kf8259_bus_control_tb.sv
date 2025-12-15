// ================================================================
// Unit Test for KF8259_Bus_Control_Logic
// Tests command word decoding and bus control signals
// ================================================================

`timescale 1ns/1ps

module kf8259_bus_control_tb;

    // DUT signals
    logic clock;
    logic reset;
    logic chip_select;
    logic read_enable;
    logic write_enable;
    logic address;
    logic [7:0] data_bus_in;
    logic ack;
    logic [7:0] internal_data_bus;
    logic write_initial_command_word_1;
    logic write_initial_command_word_2_to_4;
    logic write_operation_control_word_1;
    logic write_operation_control_word_2;
    logic write_operation_control_word_3;
    logic read;

    // Instantiate DUT
    KF8259_Bus_Control_Logic dut (
        .clock(clock),
        .reset(reset),
        .chip_select(chip_select),
        .read_enable(read_enable),
        .write_enable(write_enable),
        .address(address),
        .data_bus_in(data_bus_in),
        .ack(ack),
        .internal_data_bus(internal_data_bus),
        .write_initial_command_word_1(write_initial_command_word_1),
        .write_initial_command_word_2_to_4(write_initial_command_word_2_to_4),
        .write_operation_control_word_1(write_operation_control_word_1),
        .write_operation_control_word_2(write_operation_control_word_2),
        .write_operation_control_word_3(write_operation_control_word_3),
        .read(read)
    );

    // Clock generation
    initial begin
        clock = 0;
        forever #10 clock = ~clock;
    end

    // Test counters
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    task check_result(input string test_name, input logic condition);
        test_count++;
        if (condition) begin
            $display("[PASS] Test %0d: %s", test_count, test_name);
            pass_count++;
        end else begin
            $display("[FAIL] Test %0d: %s", test_count, test_name);
            fail_count++;
        end
    endtask

    // Test sequence
    initial begin
        $display("================================================================");
        $display("KF8259_Bus_Control_Logic Unit Test");
        $display("================================================================");

        // Initialize
        reset = 1;
        chip_select = 0;
        read_enable = 0;
        write_enable = 0;
        address = 0;
        data_bus_in = 8'h00;

        repeat(5) @(posedge clock);
        reset = 0;
        repeat(2) @(posedge clock);

        // ================================================================
        // TEST 1: ICW1 Detection (bit 4 = 1, A0 = 0)
        // ================================================================
        $display("\n--- Test 1: ICW1 Detection ---");

        chip_select = 1;
        write_enable = 1;
        address = 0;
        data_bus_in = 8'b00010011;  // D4=1 (ICW1 marker)
        @(posedge clock);

        check_result("ICW1 signal asserted", write_initial_command_word_1 == 1'b1);
        check_result("Internal data bus = input", internal_data_bus == 8'b00010011);
        check_result("ACK asserted during write", ack == 1'b1);

        chip_select = 0;
        write_enable = 0;
        @(posedge clock);

        check_result("ICW1 signal deasserted after write", write_initial_command_word_1 == 1'b0);

        // ================================================================
        // TEST 2: ICW2/3/4 Detection (A0 = 1)
        // ================================================================
        $display("\n--- Test 2: ICW2/3/4 Detection ---");

        chip_select = 1;
        write_enable = 1;
        address = 1;  // A0 = 1
        data_bus_in = 8'h20;
        @(posedge clock);

        check_result("ICW2-4 signal asserted", write_initial_command_word_2_to_4 == 1'b1);
        check_result("Internal data bus = input", internal_data_bus == 8'h20);

        chip_select = 0;
        write_enable = 0;
        @(posedge clock);

        // ================================================================
        // TEST 3: OCW1 Detection (A0 = 1)
        // ================================================================
        $display("\n--- Test 3: OCW1 Detection ---");

        chip_select = 1;
        write_enable = 1;
        address = 1;
        data_bus_in = 8'hFF;
        @(posedge clock);

        check_result("OCW1 signal asserted", write_operation_control_word_1 == 1'b1);
        check_result("Internal data bus = input", internal_data_bus == 8'hFF);

        chip_select = 0;
        write_enable = 0;
        @(posedge clock);

        // ================================================================
        // TEST 4: OCW2 Detection (A0 = 0, D4 = 0, D3 = 0)
        // ================================================================
        $display("\n--- Test 4: OCW2 Detection ---");

        chip_select = 1;
        write_enable = 1;
        address = 0;
        data_bus_in = 8'b00100000;  // EOI command (D4=0, D3=0)
        @(posedge clock);

        check_result("OCW2 signal asserted", write_operation_control_word_2 == 1'b1);
        check_result("OCW3 signal not asserted", write_operation_control_word_3 == 1'b0);
        check_result("Internal data bus = input", internal_data_bus == 8'b00100000);

        chip_select = 0;
        write_enable = 0;
        @(posedge clock);

        // ================================================================
        // TEST 5: OCW3 Detection (A0 = 0, D4 = 0, D3 = 1)
        // ================================================================
        $display("\n--- Test 5: OCW3 Detection ---");

        chip_select = 1;
        write_enable = 1;
        address = 0;
        data_bus_in = 8'b00001010;  // Read IRR (D4=0, D3=1)
        @(posedge clock);

        check_result("OCW3 signal asserted", write_operation_control_word_3 == 1'b1);
        check_result("OCW2 signal not asserted", write_operation_control_word_2 == 1'b0);
        check_result("Internal data bus = input", internal_data_bus == 8'b00001010);

        chip_select = 0;
        write_enable = 0;
        @(posedge clock);

        // ================================================================
        // TEST 6: Read Operation
        // ================================================================
        $display("\n--- Test 6: Read Operation ---");

        chip_select = 1;
        read_enable = 1;
        address = 0;
        @(posedge clock);

        check_result("Read signal asserted", read == 1'b1);
        check_result("ACK asserted during read", ack == 1'b1);
        check_result("No write signals asserted",
                     write_initial_command_word_1 == 1'b0 &&
                     write_operation_control_word_2 == 1'b0);

        chip_select = 0;
        read_enable = 0;
        @(posedge clock);

        check_result("Read signal deasserted", read == 1'b0);

        // ================================================================
        // TEST 7: Chip Select Gating
        // ================================================================
        $display("\n--- Test 7: Chip Select Gating ---");

        chip_select = 0;  // CS not active
        write_enable = 1;
        address = 0;
        data_bus_in = 8'b00010011;
        @(posedge clock);

        check_result("No ICW1 without chip select", write_initial_command_word_1 == 1'b0);
        check_result("No ACK without chip select", ack == 1'b0);
        check_result("Internal bus stays zero", internal_data_bus == 8'h00);

        write_enable = 0;
        @(posedge clock);

        // ================================================================
        // TEST 8: Sequential Command Words
        // ================================================================
        $display("\n--- Test 8: Sequential Command Words ---");

        // ICW1
        chip_select = 1;
        write_enable = 1;
        address = 0;
        data_bus_in = 8'b00010111;
        @(posedge clock);
        check_result("Sequential: ICW1 detected", write_initial_command_word_1 == 1'b1);

        // ICW2
        address = 1;
        data_bus_in = 8'h08;
        @(posedge clock);
        check_result("Sequential: ICW2 detected", write_initial_command_word_2_to_4 == 1'b1);

        // ICW4
        data_bus_in = 8'h01;
        @(posedge clock);
        check_result("Sequential: ICW4 detected", write_initial_command_word_2_to_4 == 1'b1);

        chip_select = 0;
        write_enable = 0;
        @(posedge clock);

        // ================================================================
        // TEST 9: Boundary Conditions
        // ================================================================
        $display("\n--- Test 9: Boundary Conditions ---");

        // Test with all bits set
        chip_select = 1;
        write_enable = 1;
        address = 1;
        data_bus_in = 8'hFF;
        @(posedge clock);

        check_result("All bits set handled correctly", internal_data_bus == 8'hFF);

        chip_select = 0;
        write_enable = 0;
        @(posedge clock);

        // Test with all bits clear
        chip_select = 1;
        write_enable = 1;
        address = 0;
        data_bus_in = 8'h00;
        @(posedge clock);

        check_result("All bits clear handled correctly",
                     write_operation_control_word_2 == 1'b1 &&
                     internal_data_bus == 8'h00);

        chip_select = 0;
        write_enable = 0;
        @(posedge clock);

        // ================================================================
        // Test Summary
        // ================================================================
        $display("\n================================================================");
        $display("TEST SUMMARY");
        $display("================================================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("Pass Rate:   %0d%%", (pass_count * 100) / test_count);
        $display("================================================================");

        if (fail_count == 0) begin
            $display("✓✓✓ ALL TESTS PASSED ✓✓✓");
            $finish(0);
        end else begin
            $display("✗✗✗ SOME TESTS FAILED ✗✗✗");
            $finish(1);
        end
    end

    // Timeout
    initial begin
        #10000;
        $display("\n[ERROR] Testbench timeout!");
        $finish(1);
    end

endmodule
