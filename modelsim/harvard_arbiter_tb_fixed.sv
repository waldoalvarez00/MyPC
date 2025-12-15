// ================================================================
// Unit Test for HarvardArbiter - FIXED TIMING
// Tests arbitration between I-cache and D-cache
// FIX: Added extra cycle waits for ACK checks (pipeline latency)
// ================================================================

`timescale 1ns/1ps

module harvard_arbiter_tb;

    // DUT signals
    logic clk;
    logic reset;

    // I-cache interface (read-only)
    logic [19:1] icache_m_addr;
    logic [15:0] icache_m_data_in;
    logic icache_m_access;
    logic icache_m_ack;

    // D-cache interface (read/write)
    logic [19:1] dcache_m_addr;
    logic [15:0] dcache_m_data_in;
    logic [15:0] dcache_m_data_out;
    logic dcache_m_access;
    logic dcache_m_ack;
    logic dcache_m_wr_en;
    logic [1:0] dcache_m_bytesel;

    // Memory interface
    logic [19:1] mem_m_addr;
    logic [15:0] mem_m_data_in;
    logic [15:0] mem_m_data_out;
    logic mem_m_access;
    logic mem_m_ack;
    logic mem_m_wr_en;
    logic [1:0] mem_m_bytesel;

    // Instantiate DUT
    HarvardArbiter dut (
        .clk(clk),
        .reset(reset),
        .icache_m_addr(icache_m_addr),
        .icache_m_data_in(icache_m_data_in),
        .icache_m_access(icache_m_access),
        .icache_m_ack(icache_m_ack),
        .dcache_m_addr(dcache_m_addr),
        .dcache_m_data_in(dcache_m_data_in),
        .dcache_m_data_out(dcache_m_data_out),
        .dcache_m_access(dcache_m_access),
        .dcache_m_ack(dcache_m_ack),
        .dcache_m_wr_en(dcache_m_wr_en),
        .dcache_m_bytesel(dcache_m_bytesel),
        .mem_m_addr(mem_m_addr),
        .mem_m_data_in(mem_m_data_in),
        .mem_m_data_out(mem_m_data_out),
        .mem_m_access(mem_m_access),
        .mem_m_ack(mem_m_ack),
        .mem_m_wr_en(mem_m_wr_en),
        .mem_m_bytesel(mem_m_bytesel)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #10 clk = ~clk;  // 50 MHz
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

    // Memory model - simple single-cycle ACK
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            mem_m_ack <= 1'b0;
            mem_m_data_in <= 16'b0;
        end else begin
            mem_m_ack <= mem_m_access;
            if (mem_m_access && !mem_m_wr_en)
                mem_m_data_in <= {mem_m_addr[19:5], 1'b0};  // Return address as data
        end
    end

    // Test sequence
    initial begin
        $display("================================================================");
        $display("HarvardArbiter Unit Test - FIXED TIMING");
        $display("================================================================");

        // Initialize
        reset = 1;
        icache_m_addr = 19'b0;
        icache_m_access = 0;
        dcache_m_addr = 19'b0;
        dcache_m_data_out = 16'b0;
        dcache_m_access = 0;
        dcache_m_wr_en = 0;
        dcache_m_bytesel = 2'b11;

        repeat(5) @(posedge clk);
        reset = 0;
        repeat(5) @(posedge clk);

        // ================================================================
        // TEST 1: Reset Behavior
        // ================================================================
        $display("\n--- Test 1: Reset Behavior ---");

        check_result("Arbiter idle after reset", !mem_m_access);
        check_result("No I-cache ack after reset", !icache_m_ack);
        check_result("No D-cache ack after reset", !dcache_m_ack);

        // ================================================================
        // TEST 2: Single I-cache Request
        // ================================================================
        $display("\n--- Test 2: Single I-cache Request ---");

        icache_m_addr = 19'h12345;
        icache_m_access = 1;
        @(posedge clk);  // Cycle 1: State transitions
        @(posedge clk);  // Cycle 2: Check forwarding

        check_result("I-cache request forwarded to memory", mem_m_access);
        check_result("Memory address matches I-cache", mem_m_addr == 19'h12345);
        check_result("Memory access is read (wr_en low)", !mem_m_wr_en);

        // FIX: Wait 2 more cycles for ACK (arbiter pipeline + memory latency)
        @(posedge clk);  // Cycle 3: mem_ack registered
        @(posedge clk);  // Cycle 4: icache_ack registered
        check_result("I-cache receives ack", icache_m_ack);
        check_result("I-cache receives data", icache_m_data_in == {icache_m_addr[19:5], 1'b0});

        icache_m_access = 0;
        @(posedge clk);

        // ================================================================
        // TEST 3: Single D-cache Read Request
        // ================================================================
        $display("\n--- Test 3: Single D-cache Read Request ---");

        dcache_m_addr = 19'h54321;
        dcache_m_access = 1;
        dcache_m_wr_en = 0;
        @(posedge clk);
        @(posedge clk);

        check_result("D-cache read forwarded to memory", mem_m_access);
        check_result("Memory address matches D-cache", mem_m_addr == 19'h54321);
        check_result("Memory access is read", !mem_m_wr_en);

        // FIX: Wait 2 more cycles for ACK
        @(posedge clk);
        @(posedge clk);
        check_result("D-cache receives ack", dcache_m_ack);

        dcache_m_access = 0;
        @(posedge clk);

        // ================================================================
        // TEST 4: Single D-cache Write Request
        // ================================================================
        $display("\n--- Test 4: Single D-cache Write Request ---");

        dcache_m_addr = 19'hABCDE;
        dcache_m_data_out = 16'hBEEF;
        dcache_m_access = 1;
        dcache_m_wr_en = 1;
        dcache_m_bytesel = 2'b11;
        @(posedge clk);
        @(posedge clk);

        check_result("D-cache write forwarded to memory", mem_m_access);
        check_result("Memory address matches D-cache write", mem_m_addr == 19'hABCDE);
        check_result("Memory write enable set", mem_m_wr_en);
        check_result("Memory data matches D-cache", mem_m_data_out == 16'hBEEF);
        check_result("Memory bytesel matches D-cache", mem_m_bytesel == 2'b11);

        // FIX: Wait 2 more cycles for ACK
        @(posedge clk);
        @(posedge clk);
        check_result("D-cache write receives ack", dcache_m_ack);

        dcache_m_access = 0;
        dcache_m_wr_en = 0;
        @(posedge clk);

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

endmodule
