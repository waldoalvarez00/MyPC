`timescale 1ns / 1ps

/*
 * Testbench for SDRAMConfigRegister
 *
 * Tests the simple SDRAM configuration status register
 * that reports initialization completion status.
 */

module sdram_config_tb();

    // Clock
    logic clk;

    // Control signals
    logic cs;
    logic [15:0] data_m_data_out;
    logic data_m_wr_en;
    logic data_m_access;
    logic data_m_ack;
    logic config_done;

    // Test control
    integer test_num;
    integer pass_count;
    integer fail_count;

    // Instantiate the Unit Under Test (UUT)
    SDRAMConfigRegister uut (
        .clk(clk),
        .cs(cs),
        .data_m_data_out(data_m_data_out),
        .data_m_wr_en(data_m_wr_en),
        .data_m_access(data_m_access),
        .data_m_ack(data_m_ack),
        .config_done(config_done)
    );

    // Clock generation (100MHz = 10ns period)
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test reporting
    task report_test(input string test_name, input logic pass);
        begin
            if (pass) begin
                $display("✓ Test %0d PASSED: %s", test_num, test_name);
                pass_count++;
            end else begin
                $display("✗ Test %0d FAILED: %s", test_num, test_name);
                fail_count++;
            end
            test_num++;
        end
    endtask

    // Helper task: Read from config register
    task read_config(output [15:0] data);
        begin
            @(posedge clk);
            cs = 1'b1;
            data_m_access = 1'b1;
            data_m_wr_en = 1'b0;
            @(posedge clk);
            data = data_m_data_out;
            @(posedge clk);
            cs = 1'b0;
            data_m_access = 1'b0;
            @(posedge clk);
        end
    endtask

    // Main test sequence
    initial begin
        // Local test variables
        logic [15:0] read_data;
        logic test3a, test3b;
        logic ack_asserted;
        logic ack_on_write, data_zero_on_write;
        logic trans_a, trans_b, trans_c;

        // Initialize signals
        cs = 0;
        data_m_wr_en = 0;
        data_m_access = 0;
        config_done = 0;
        test_num = 1;
        pass_count = 0;
        fail_count = 0;

        $display("\n================================================================");
        $display("SDRAM Config Register Testbench");
        $display("================================================================\n");

        #20;
        @(posedge clk);

        // Test 1: Read when config_done = 0
        $display("\n[Test %0d] Read when config_done = 0", test_num);
        config_done = 1'b0;
        read_config(read_data);
        report_test("Config not done - returns 0", read_data == 16'h0000);

        // Test 2: Read when config_done = 1
        $display("\n[Test %0d] Read when config_done = 1", test_num);
        config_done = 1'b1;
        read_config(read_data);
        report_test("Config done - returns 1", read_data == 16'h0001);

        // Test 3: Multiple reads with config_done = 1
        $display("\n[Test %0d] Multiple reads with config_done = 1", test_num);
        config_done = 1'b1;
        read_config(read_data);
        test3a = (read_data == 16'h0001);
        read_config(read_data);
        test3b = (read_data == 16'h0001);
        report_test("Multiple reads consistent", test3a && test3b);

        // Test 4: ACK signal assertion
        $display("\n[Test %0d] ACK signal assertion", test_num);
        @(posedge clk);
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b0;
        @(posedge clk);
        @(posedge clk);
        ack_asserted = data_m_ack;
        cs = 1'b0;
        data_m_access = 1'b0;
        @(posedge clk);
        report_test("ACK asserted during access", ack_asserted);

        // Test 5: No access - no ACK
        $display("\n[Test %0d] No access - no ACK", test_num);
        @(posedge clk);
        cs = 1'b0;
        data_m_access = 1'b0;
        @(posedge clk);
        @(posedge clk);
        report_test("No ACK when not accessed", data_m_ack == 1'b0);

        // Test 6: CS not asserted - no response
        $display("\n[Test %0d] CS not asserted", test_num);
        @(posedge clk);
        cs = 1'b0;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b0;
        @(posedge clk);
        @(posedge clk);
        report_test("No response without CS", data_m_ack == 1'b0);
        cs = 1'b0;
        data_m_access = 1'b0;
        @(posedge clk);

        // Test 7: Write attempt (should be ignored, register is read-only)
        $display("\n[Test %0d] Write attempt (read-only register)", test_num);
        @(posedge clk);
        cs = 1'b1;
        data_m_access = 1'b1;
        data_m_wr_en = 1'b1;
        @(posedge clk);
        @(posedge clk);
        ack_on_write = data_m_ack;
        data_zero_on_write = (data_m_data_out == 16'h0000);
        cs = 1'b0;
        data_m_access = 1'b0;
        data_m_wr_en = 1'b0;
        @(posedge clk);
        report_test("Write returns no data", ack_on_write && data_zero_on_write);

        // Test 8: Transition config_done 0->1->0
        $display("\n[Test %0d] Config done transitions", test_num);
        config_done = 1'b0;
        read_config(read_data);
        trans_a = (read_data == 16'h0000);
        config_done = 1'b1;
        read_config(read_data);
        trans_b = (read_data == 16'h0001);
        config_done = 1'b0;
        read_config(read_data);
        trans_c = (read_data == 16'h0000);
        report_test("Config done transitions tracked", trans_a && trans_b && trans_c);

        // Final summary
        #100;
        $display("\n================================================================");
        $display("Test Summary");
        $display("================================================================");
        $display("Total Tests: %0d", test_num - 1);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("Success Rate: %0d%%", (pass_count * 100) / (test_num - 1));

        if (fail_count == 0) begin
            $display("\n✓✓✓ SUCCESS: All SDRAM Config Register tests passed! ✓✓✓\n");
        end else begin
            $display("\n✗✗✗ FAILURE: %0d test(s) failed ✗✗✗\n", fail_count);
        end

        $display("================================================================\n");
        $finish;
    end

    // Timeout watchdog
    initial begin
        #50000;  // 50us timeout
        $display("\n✗✗✗ ERROR: Simulation timeout! ✗✗✗\n");
        $finish;
    end

endmodule
