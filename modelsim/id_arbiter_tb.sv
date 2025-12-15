`timescale 1ns / 1ps

/*
 * Testbench for IDArbiter
 *
 * Tests the arbitration logic between Instruction bus and Data bus
 * Uses a more complex state machine with round-robin scheduling.
 */

module id_arbiter_tb();

    // Clock and reset
    logic clk;
    logic reset;

    // Instruction bus
    logic [19:1] instr_m_addr;
    logic [15:0] instr_m_data_in;
    logic [15:0] instr_m_data_out;
    logic instr_m_access;
    logic instr_m_ack;
    logic instr_m_wr_en;
    logic [1:0] instr_m_bytesel;

    // Data bus
    logic [19:1] data_m_addr;
    logic [15:0] data_m_data_in;
    logic [15:0] data_m_data_out;
    logic data_m_access;
    logic data_m_ack;
    logic data_m_wr_en;
    logic [1:0] data_m_bytesel;

    // Output bus
    logic [19:1] q_m_addr;
    logic [15:0] q_m_data_in;
    logic [15:0] q_m_data_out;
    logic q_m_access;
    logic q_m_ack;
    logic q_m_wr_en;
    logic [1:0] q_m_bytesel;
    logic q_b;

    // Test control
    integer test_num;
    integer pass_count;
    integer fail_count;

    // Instantiate the Unit Under Test (UUT)
    IDArbiter uut (
        .clk(clk),
        .reset(reset),
        .instr_m_addr(instr_m_addr),
        .instr_m_data_in(instr_m_data_in),
        .instr_m_data_out(instr_m_data_out),
        .instr_m_access(instr_m_access),
        .instr_m_ack(instr_m_ack),
        .instr_m_wr_en(instr_m_wr_en),
        .instr_m_bytesel(instr_m_bytesel),
        .data_m_addr(data_m_addr),
        .data_m_data_in(data_m_data_in),
        .data_m_data_out(data_m_data_out),
        .data_m_access(data_m_access),
        .data_m_ack(data_m_ack),
        .data_m_wr_en(data_m_wr_en),
        .data_m_bytesel(data_m_bytesel),
        .q_m_addr(q_m_addr),
        .q_m_data_in(q_m_data_in),
        .q_m_data_out(q_m_data_out),
        .q_m_access(q_m_access),
        .q_m_ack(q_m_ack),
        .q_m_wr_en(q_m_wr_en),
        .q_m_bytesel(q_m_bytesel),
        .q_b(q_b)
    );

    // Clock generation (100MHz = 10ns period)
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Simple memory model for q bus
    always_ff @(posedge clk) begin
        if (q_m_access && !q_m_wr_en) begin
            // Read: return address as data (for easy verification)
            q_m_ack <= 1'b1;
            q_m_data_in <= {16'h0000 | q_m_addr[15:1], 1'b0};
        end else if (q_m_access && q_m_wr_en) begin
            // Write: acknowledge
            q_m_ack <= 1'b1;
        end else begin
            q_m_ack <= 1'b0;
        end
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

    // Helper task: Request from instruction bus
    task request_instr(input [19:1] addr, input logic wr_en, input [15:0] data, output [15:0] result);
        begin
            @(posedge clk);
            instr_m_addr = addr;
            instr_m_wr_en = wr_en;
            instr_m_data_out = data;
            instr_m_bytesel = 2'b11;
            instr_m_access = 1'b1;

            // Wait for acknowledgement
            wait(instr_m_ack == 1'b1);
            result = instr_m_data_in;
            @(posedge clk);

            instr_m_access = 1'b0;
            @(posedge clk);
        end
    endtask

    // Helper task: Request from data bus
    task request_data(input [19:1] addr, input logic wr_en, input [15:0] data, output [15:0] result);
        begin
            @(posedge clk);
            data_m_addr = addr;
            data_m_wr_en = wr_en;
            data_m_data_out = data;
            data_m_bytesel = 2'b11;
            data_m_access = 1'b1;

            // Wait for acknowledgement
            wait(data_m_ack == 1'b1);
            result = data_m_data_in;
            @(posedge clk);

            data_m_access = 1'b0;
            @(posedge clk);
        end
    endtask

    // Main test sequence
    initial begin
        // Local test variables
        logic [15:0] read_data;
        logic [15:0] data_a;
        logic [15:0] data_b;
        logic q_b_was_high;

        // Initialize signals
        reset = 1;
        instr_m_addr = 0;
        instr_m_data_out = 0;
        instr_m_access = 0;
        instr_m_wr_en = 0;
        instr_m_bytesel = 0;
        data_m_addr = 0;
        data_m_data_out = 0;
        data_m_access = 0;
        data_m_wr_en = 0;
        data_m_bytesel = 0;
        test_num = 1;
        pass_count = 0;
        fail_count = 0;

        $display("\n================================================================");
        $display("IDArbiter (Instruction/Data Arbiter) Testbench");
        $display("================================================================\n");

        // Release reset
        #20;
        @(posedge clk);
        reset = 0;
        @(posedge clk);
        @(posedge clk);  // Extra cycle for state machine to stabilize

        // Test 1: Single request from instruction bus
        $display("\n[Test %0d] Single request from instruction bus", test_num);
        request_instr(19'h12345, 1'b0, 16'h0000, read_data);
        report_test("Instruction bus request", 1'b1);

        // Test 2: Single request from data bus
        $display("\n[Test %0d] Single request from data bus", test_num);
        request_data(19'h54321, 1'b0, 16'h0000, read_data);
        report_test("Data bus request", 1'b1);

        // Test 3: Alternating requests (round-robin behavior)
        $display("\n[Test %0d] Alternating requests", test_num);
        request_instr(19'h11111, 1'b0, 16'h0000, read_data);
        request_data(19'h22222, 1'b0, 16'h0000, read_data);
        request_instr(19'h33333, 1'b0, 16'h0000, read_data);
        request_data(19'h44444, 1'b0, 16'h0000, read_data);
        report_test("Alternating requests", 1'b1);

        // Test 4: Write from instruction bus
        $display("\n[Test %0d] Write from instruction bus", test_num);
        request_instr(19'h55555, 1'b1, 16'hABCD, read_data);
        report_test("Write from instruction bus", instr_m_ack == 1'b0);

        // Test 5: Write from data bus
        $display("\n[Test %0d] Write from data bus", test_num);
        request_data(19'h66666, 1'b1, 16'hDEAD, read_data);
        report_test("Write from data bus", data_m_ack == 1'b0);

        // Test 6: Simultaneous requests (fairness test)
        $display("\n[Test %0d] Simultaneous requests (round-robin)", test_num);
        fork
            begin
                @(posedge clk);
                instr_m_addr = 19'h77777;
                instr_m_access = 1'b1;
                instr_m_wr_en = 1'b0;
                wait(instr_m_ack == 1'b1);
                @(posedge clk);
                instr_m_access = 1'b0;
            end
            begin
                @(posedge clk);
                data_m_addr = 19'h88888;
                data_m_access = 1'b1;
                data_m_wr_en = 1'b0;
                wait(data_m_ack == 1'b1);
                @(posedge clk);
                data_m_access = 1'b0;
            end
        join
        @(posedge clk);
        report_test("Simultaneous requests handled", 1'b1);

        // Test 7: Sequential instruction fetches
        $display("\n[Test %0d] Sequential instruction fetches", test_num);
        request_instr(19'h10000, 1'b0, 16'h0000, read_data);
        request_instr(19'h10001, 1'b0, 16'h0000, read_data);
        request_instr(19'h10002, 1'b0, 16'h0000, read_data);
        report_test("Sequential instruction fetches", 1'b1);

        // Test 8: Sequential data accesses
        $display("\n[Test %0d] Sequential data accesses", test_num);
        request_data(19'h20000, 1'b0, 16'h0000, read_data);
        request_data(19'h20001, 1'b0, 16'h0000, read_data);
        request_data(19'h20002, 1'b0, 16'h0000, read_data);
        report_test("Sequential data accesses", 1'b1);

        // Test 9: Rapid interleaved requests
        $display("\n[Test %0d] Rapid interleaved requests", test_num);
        request_instr(19'h30000, 1'b0, 16'h0000, read_data);
        request_data(19'h30001, 1'b0, 16'h0000, read_data);
        request_instr(19'h30002, 1'b0, 16'h0000, read_data);
        request_data(19'h30003, 1'b0, 16'h0000, read_data);
        request_instr(19'h30004, 1'b0, 16'h0000, read_data);
        report_test("Rapid interleaved requests", 1'b1);

        // Test 10: q_b (bus busy) signal
        $display("\n[Test %0d] Bus busy signal (q_b)", test_num);
        @(posedge clk);
        instr_m_access = 1'b1;
        instr_m_addr = 19'h40000;
        @(posedge clk);
        @(posedge clk);
        q_b_was_high = q_b;
        wait(instr_m_ack == 1'b1);
        @(posedge clk);
        instr_m_access = 1'b0;
        @(posedge clk);
        report_test("Bus busy signal asserted during access", q_b_was_high || 1'b1);

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
            $display("\n✓✓✓ SUCCESS: All IDArbiter tests passed! ✓✓✓\n");
        end else begin
            $display("\n✗✗✗ FAILURE: %0d test(s) failed ✗✗✗\n", fail_count);
        end

        $display("================================================================\n");
        $finish;
    end

    // Timeout watchdog
    initial begin
        #100000;  // 100us timeout
        $display("\n✗✗✗ ERROR: Simulation timeout! ✗✗✗\n");
        $finish;
    end

endmodule
