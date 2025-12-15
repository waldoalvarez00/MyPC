// ================================================================
// Unit Test for HarvardArbiter
// Tests arbitration between I-cache and D-cache
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

    // Test variables (declared at module level for Icarus Verilog)
    logic first_served_icache;
    int icache_reqs;
    int dcache_reqs;
    int icache_acks;
    int dcache_acks;

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
        $display("HarvardArbiter Unit Test");
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
        @(posedge clk);
        @(posedge clk);

        check_result("I-cache request forwarded to memory", mem_m_access);
        check_result("Memory address matches I-cache", mem_m_addr == 19'h12345);
        check_result("Memory access is read (wr_en low)", !mem_m_wr_en);

        @(posedge clk);
        @(posedge clk);  // Extra cycle for registered ack
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

        @(posedge clk);
        @(posedge clk);  // Extra cycle for registered ack
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

        @(posedge clk);
        @(posedge clk);  // Extra cycle for registered ack
        check_result("D-cache write receives ack", dcache_m_ack);

        dcache_m_access = 0;
        dcache_m_wr_en = 0;
        @(posedge clk);

        // ================================================================
        // TEST 5: D-cache Write Priority Over I-cache
        // ================================================================
        $display("\n--- Test 5: D-cache Write Priority ---");

        // Both request simultaneously, D-cache write should win
        icache_m_addr = 19'h11111;
        icache_m_access = 1;
        dcache_m_addr = 19'h22222;
        dcache_m_data_out = 16'hDEAD;
        dcache_m_access = 1;
        dcache_m_wr_en = 1;
        @(posedge clk);
        @(posedge clk);

        check_result("D-cache write has priority", mem_m_addr == 19'h22222);
        check_result("Memory write enable for D-cache", mem_m_wr_en);

        @(posedge clk);
        @(posedge clk);  // Extra cycle for registered ack
        check_result("D-cache write acked first", dcache_m_ack);
        check_result("I-cache not yet acked", !icache_m_ack);

        dcache_m_access = 0;
        dcache_m_wr_en = 0;
        @(posedge clk);

        // I-cache should be served next
        // Need 4 cycles: state transition + mem_access + mem_ack + arbiter ack_reg
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);  // Extra cycle for registered ack
        check_result("I-cache served after D-cache write", icache_m_ack);

        icache_m_access = 0;
        @(posedge clk);

        // ================================================================
        // TEST 6: Round-Robin for Simultaneous Reads
        // ================================================================
        $display("\n--- Test 6: Round-Robin Arbitration ---");

        // First simultaneous read (should serve I-cache, as last_served_dcache=1)
        icache_m_addr = 19'h33333;
        icache_m_access = 1;
        dcache_m_addr = 19'h44444;
        dcache_m_access = 1;
        dcache_m_wr_en = 0;
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);  // Extra cycle for registered ack

        first_served_icache = icache_m_ack;

        @(posedge clk);
        icache_m_access = 0;
        dcache_m_access = 0;
        @(posedge clk);

        // Second simultaneous read (should serve D-cache this time)
        icache_m_addr = 19'h55555;
        icache_m_access = 1;
        dcache_m_addr = 19'h66666;
        dcache_m_access = 1;
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);  // Extra cycle for registered ack

        check_result("Round-robin alternates between caches",
                     first_served_icache && dcache_m_ack);

        icache_m_access = 0;
        dcache_m_access = 0;
        @(posedge clk);

        // ================================================================
        // TEST 7: Back-to-Back I-cache Requests
        // ================================================================
        $display("\n--- Test 7: Back-to-Back I-cache Requests ---");

        icache_m_addr = 19'h77777;
        icache_m_access = 1;
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);  // Extra cycle for registered ack

        check_result("First I-cache request acked", icache_m_ack);

        // Second request immediately
        icache_m_addr = 19'h88888;
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);  // Extra cycle for registered ack

        check_result("Second I-cache request acked", icache_m_ack);

        icache_m_access = 0;
        @(posedge clk);

        // ================================================================
        // TEST 8: Back-to-Back D-cache Requests
        // ================================================================
        $display("\n--- Test 8: Back-to-Back D-cache Requests ---");

        dcache_m_addr = 19'h99999;
        dcache_m_access = 1;
        dcache_m_wr_en = 0;
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);  // Extra cycle for registered ack

        check_result("First D-cache request acked", dcache_m_ack);

        // Second request immediately
        dcache_m_addr = 19'hAAAAA;
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);  // Extra cycle for registered ack

        check_result("Second D-cache request acked", dcache_m_ack);

        dcache_m_access = 0;
        @(posedge clk);

        // ================================================================
        // TEST 9: Request Dropping
        // ================================================================
        $display("\n--- Test 9: Request Dropping ---");

        icache_m_addr = 19'hBBBBB;
        icache_m_access = 1;
        @(posedge clk);

        // Drop request before ack
        icache_m_access = 0;
        @(posedge clk);
        @(posedge clk);

        check_result("Arbiter returns to IDLE after dropped request", !mem_m_access);

        // ================================================================
        // TEST 10: Byte Select Propagation
        // ================================================================
        $display("\n--- Test 10: Byte Select Propagation ---");

        dcache_m_addr = 19'hCCCCC;
        dcache_m_data_out = 16'h00FF;
        dcache_m_access = 1;
        dcache_m_wr_en = 1;
        dcache_m_bytesel = 2'b01;  // Low byte only
        @(posedge clk);
        @(posedge clk);

        check_result("Low byte select propagated", mem_m_bytesel == 2'b01);

        @(posedge clk);
        dcache_m_access = 0;
        dcache_m_wr_en = 0;
        @(posedge clk);

        dcache_m_data_out = 16'hFF00;
        dcache_m_access = 1;
        dcache_m_wr_en = 1;
        dcache_m_bytesel = 2'b10;  // High byte only
        @(posedge clk);
        @(posedge clk);

        check_result("High byte select propagated", mem_m_bytesel == 2'b10);

        dcache_m_access = 0;
        dcache_m_wr_en = 0;
        @(posedge clk);

        // ================================================================
        // TEST 11: Sustained Mixed Traffic
        // ================================================================
        $display("\n--- Test 11: Sustained Mixed Traffic ---");

        icache_reqs = 0;
        dcache_reqs = 0;
        icache_acks = 0;
        dcache_acks = 0;

        for (int i = 0; i < 20; i++) begin
            // Random access pattern
            icache_m_access = (i % 3 != 0);
            dcache_m_access = (i % 2 == 0);
            dcache_m_wr_en = (i % 4 == 0);

            if (icache_m_access) icache_reqs++;
            if (dcache_m_access) dcache_reqs++;

            @(posedge clk);

            if (icache_m_ack) icache_acks++;
            if (dcache_m_ack) dcache_acks++;
        end

        icache_m_access = 0;
        dcache_m_access = 0;
        repeat(5) @(posedge clk);

        // Final acks
        if (icache_m_ack) icache_acks++;
        if (dcache_m_ack) dcache_acks++;

        $display("INFO: Mixed traffic - I-cache: %0d reqs, %0d acks | D-cache: %0d reqs, %0d acks",
                 icache_reqs, icache_acks, dcache_reqs, dcache_acks);
        check_result("Sustained traffic handled without lockup",
                     (icache_acks > 0) && (dcache_acks > 0));

        // ================================================================
        // TEST 12: No Spurious Acks
        // ================================================================
        $display("\n--- Test 12: No Spurious Acks ---");

        icache_m_access = 0;
        dcache_m_access = 0;
        repeat(10) @(posedge clk);

        check_result("No I-cache ack when idle", !icache_m_ack);
        check_result("No D-cache ack when idle", !dcache_m_ack);
        check_result("No memory access when idle", !mem_m_access);

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
        #100000;  // 100us timeout
        $display("\n[ERROR] Testbench timeout!");
        $finish(1);
    end

endmodule
