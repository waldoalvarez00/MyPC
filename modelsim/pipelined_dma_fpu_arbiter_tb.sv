// ================================================================
// Unit Test for PipelinedDMAFPUArbiter
// Tests 3-port pipelined arbitration (DMA, FPU, CPU)
// ================================================================

`timescale 1ns/1ps

module pipelined_dma_fpu_arbiter_tb;

    // DUT signals
    logic clk;
    logic reset;

    // DMA bus (A-bus) - Highest priority
    logic [19:1] a_m_addr;
    logic [15:0] a_m_data_in;
    logic [15:0] a_m_data_out;
    logic a_m_access;
    logic a_m_ack;
    logic a_m_wr_en;
    logic [1:0] a_m_bytesel;
    logic ioa;

    // CPU Cache bus (B-bus) - Lowest priority
    logic [19:1] b_m_addr;
    logic [15:0] b_m_data_in;
    logic [15:0] b_m_data_out;
    logic b_m_access;
    logic b_m_ack;
    logic b_m_wr_en;
    logic [1:0] b_m_bytesel;
    logic iob;

    // FPU bus (C-bus) - Medium priority
    logic [19:1] c_m_addr;
    logic [15:0] c_m_data_in;
    logic [15:0] c_m_data_out;
    logic c_m_access;
    logic c_m_ack;
    logic c_m_wr_en;
    logic [1:0] c_m_bytesel;

    // Output bus to memory
    logic [19:1] q_m_addr;
    logic [15:0] q_m_data_in;
    logic [15:0] q_m_data_out;
    logic q_m_access;
    logic q_m_ack;
    logic q_m_wr_en;
    logic [1:0] q_m_bytesel;
    logic ioq;
    logic [1:0] q_grant;

    // Instantiate DUT
    PipelinedDMAFPUArbiter dut (
        .clk(clk),
        .reset(reset),
        .a_m_addr(a_m_addr),
        .a_m_data_in(a_m_data_in),
        .a_m_data_out(a_m_data_out),
        .a_m_access(a_m_access),
        .a_m_ack(a_m_ack),
        .a_m_wr_en(a_m_wr_en),
        .a_m_bytesel(a_m_bytesel),
        .ioa(ioa),
        .b_m_addr(b_m_addr),
        .b_m_data_in(b_m_data_in),
        .b_m_data_out(b_m_data_out),
        .b_m_access(b_m_access),
        .b_m_ack(b_m_ack),
        .b_m_wr_en(b_m_wr_en),
        .b_m_bytesel(b_m_bytesel),
        .iob(iob),
        .c_m_addr(c_m_addr),
        .c_m_data_in(c_m_data_in),
        .c_m_data_out(c_m_data_out),
        .c_m_access(c_m_access),
        .c_m_ack(c_m_ack),
        .c_m_wr_en(c_m_wr_en),
        .c_m_bytesel(c_m_bytesel),
        .q_m_addr(q_m_addr),
        .q_m_data_in(q_m_data_in),
        .q_m_data_out(q_m_data_out),
        .q_m_access(q_m_access),
        .q_m_ack(q_m_ack),
        .q_m_wr_en(q_m_wr_en),
        .q_m_bytesel(q_m_bytesel),
        .ioq(ioq),
        .q_grant(q_grant)
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
    logic [1:0] observed_grant;
    int ack_count;
    int a_reqs;
    int b_reqs;
    int c_reqs;
    int a_acks;
    int b_acks;
    int c_acks;

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

    // Memory model - single-cycle ACK with pipeline delay
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            q_m_ack <= 1'b0;
            q_m_data_in <= 16'b0;
        end else begin
            q_m_ack <= q_m_access;
            if (q_m_access && !q_m_wr_en)
                q_m_data_in <= {q_m_addr[19:5], 1'b0};  // Return address as data
        end
    end

    // Test sequence
    initial begin
        $display("================================================================");
        $display("PipelinedDMAFPUArbiter Unit Test");
        $display("================================================================");

        // Initialize
        reset = 1;
        a_m_addr = 19'b0;
        a_m_data_out = 16'b0;
        a_m_access = 0;
        a_m_wr_en = 0;
        a_m_bytesel = 2'b11;
        ioa = 0;
        b_m_addr = 19'b0;
        b_m_data_out = 16'b0;
        b_m_access = 0;
        b_m_wr_en = 0;
        b_m_bytesel = 2'b11;
        iob = 0;
        c_m_addr = 19'b0;
        c_m_data_out = 16'b0;
        c_m_access = 0;
        c_m_wr_en = 0;
        c_m_bytesel = 2'b11;

        repeat(5) @(posedge clk);
        reset = 0;
        repeat(5) @(posedge clk);

        // ================================================================
        // TEST 1: Reset Behavior
        // ================================================================
        $display("\n--- Test 1: Reset Behavior ---");

        check_result("Arbiter idle after reset", !q_m_access);
        check_result("No A-bus ack after reset", !a_m_ack);
        check_result("No B-bus ack after reset", !b_m_ack);
        check_result("No C-bus ack after reset", !c_m_ack);
        check_result("Grant is none after reset", q_grant == 2'b00);

        // ================================================================
        // TEST 2: Single DMA (A-bus) Request
        // ================================================================
        $display("\n--- Test 2: Single DMA Request ---");

        a_m_addr = 19'h12345;
        a_m_access = 1;
        repeat(5) @(posedge clk);  // Pipeline latency

        check_result("A-bus request forwarded to memory", q_m_access);
        check_result("Memory address matches A-bus", q_m_addr == 19'h12345);
        check_result("Grant is A-bus", q_grant == 2'b01);

        @(posedge clk);
        check_result("A-bus receives ack", a_m_ack);

        a_m_access = 0;
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 3: Single CPU (B-bus) Request
        // ================================================================
        $display("\n--- Test 3: Single CPU Request ---");

        b_m_addr = 19'h54321;
        b_m_access = 1;
        repeat(5) @(posedge clk);

        check_result("B-bus request forwarded to memory", q_m_access);
        check_result("Memory address matches B-bus", q_m_addr == 19'h54321);
        check_result("Grant is B-bus", q_grant == 2'b10);

        @(posedge clk);
        check_result("B-bus receives ack", b_m_ack);

        b_m_access = 0;
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 4: Single FPU (C-bus) Request
        // ================================================================
        $display("\n--- Test 4: Single FPU Request ---");

        c_m_addr = 19'hABCDE;
        c_m_access = 1;
        repeat(5) @(posedge clk);

        check_result("C-bus request forwarded to memory", q_m_access);
        check_result("Memory address matches C-bus", q_m_addr == 19'hABCDE);
        check_result("Grant is C-bus", q_grant == 2'b11);

        @(posedge clk);
        check_result("C-bus receives ack", c_m_ack);

        c_m_access = 0;
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 5: DMA Priority Over FPU
        // ================================================================
        $display("\n--- Test 5: DMA Priority Over FPU ---");

        // Both request simultaneously
        a_m_addr = 19'h11111;
        a_m_access = 1;
        c_m_addr = 19'h22222;
        c_m_access = 1;
        repeat(5) @(posedge clk);

        check_result("DMA has priority over FPU", q_grant == 2'b01);
        check_result("DMA address served first", q_m_addr == 19'h11111);

        @(posedge clk);
        check_result("DMA acked first", a_m_ack && !c_m_ack);

        a_m_access = 0;
        repeat(3) @(posedge clk);

        // FPU should be served next
        check_result("FPU served after DMA", q_grant == 2'b11);

        c_m_access = 0;
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 6: DMA Priority Over CPU
        // ================================================================
        $display("\n--- Test 6: DMA Priority Over CPU ---");

        a_m_addr = 19'h33333;
        a_m_access = 1;
        b_m_addr = 19'h44444;
        b_m_access = 1;
        repeat(5) @(posedge clk);

        check_result("DMA has priority over CPU", q_grant == 2'b01);

        @(posedge clk);
        check_result("DMA acked first", a_m_ack && !b_m_ack);

        a_m_access = 0;
        repeat(3) @(posedge clk);

        check_result("CPU served after DMA", q_grant == 2'b10);

        b_m_access = 0;
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 7: FPU Priority Over CPU
        // ================================================================
        $display("\n--- Test 7: FPU Priority Over CPU ---");

        c_m_addr = 19'h55555;
        c_m_access = 1;
        b_m_addr = 19'h66666;
        b_m_access = 1;
        repeat(5) @(posedge clk);

        check_result("FPU has priority over CPU", q_grant == 2'b11);

        @(posedge clk);
        check_result("FPU acked first", c_m_ack && !b_m_ack);

        c_m_access = 0;
        repeat(3) @(posedge clk);

        check_result("CPU served after FPU", q_grant == 2'b10);

        b_m_access = 0;
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 8: All Three Buses Request Simultaneously
        // ================================================================
        $display("\n--- Test 8: Three-Way Priority ---");

        a_m_addr = 19'h77777;
        a_m_access = 1;
        b_m_addr = 19'h88888;
        b_m_access = 1;
        c_m_addr = 19'h99999;
        c_m_access = 1;
        repeat(5) @(posedge clk);

        check_result("DMA wins three-way arbitration", q_grant == 2'b01);

        @(posedge clk);
        a_m_access = 0;
        repeat(3) @(posedge clk);

        check_result("FPU served second in three-way", q_grant == 2'b11);

        @(posedge clk);
        c_m_access = 0;
        repeat(3) @(posedge clk);

        check_result("CPU served last in three-way", q_grant == 2'b10);

        b_m_access = 0;
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 9: DMA Write Operation
        // ================================================================
        $display("\n--- Test 9: DMA Write ---");

        a_m_addr = 19'hAAAAA;
        a_m_data_out = 16'hBEEF;
        a_m_access = 1;
        a_m_wr_en = 1;
        a_m_bytesel = 2'b11;
        ioa = 0;
        repeat(5) @(posedge clk);

        check_result("DMA write forwarded", q_m_access && q_m_wr_en);
        check_result("Write data propagated", q_m_data_out == 16'hBEEF);
        check_result("Bytesel propagated", q_m_bytesel == 2'b11);

        a_m_access = 0;
        a_m_wr_en = 0;
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 10: FPU Write Operation
        // ================================================================
        $display("\n--- Test 10: FPU Write ---");

        c_m_addr = 19'hBBBBB;
        c_m_data_out = 16'hDEAD;
        c_m_access = 1;
        c_m_wr_en = 1;
        c_m_bytesel = 2'b10;  // High byte only
        repeat(5) @(posedge clk);

        check_result("FPU write forwarded", q_m_access && q_m_wr_en);
        check_result("FPU write data propagated", q_m_data_out == 16'hDEAD);
        check_result("FPU bytesel propagated", q_m_bytesel == 2'b10);
        check_result("FPU never sets ioq", !ioq);

        c_m_access = 0;
        c_m_wr_en = 0;
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 11: I/O Flag Propagation
        // ================================================================
        $display("\n--- Test 11: I/O Flag Propagation ---");

        a_m_addr = 19'hCCCCC;
        a_m_access = 1;
        ioa = 1;  // I/O access
        repeat(5) @(posedge clk);

        check_result("A-bus I/O flag propagated", ioq == 1'b1);

        a_m_access = 0;
        ioa = 0;
        repeat(3) @(posedge clk);

        b_m_addr = 19'hDDDDD;
        b_m_access = 1;
        iob = 1;  // I/O access
        repeat(5) @(posedge clk);

        check_result("B-bus I/O flag propagated", ioq == 1'b1);

        b_m_access = 0;
        iob = 0;
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 12: Back-to-Back Pipelined Requests
        // ================================================================
        $display("\n--- Test 12: Pipelined Throughput ---");

        // Start first request
        a_m_addr = 19'h10000;
        a_m_access = 1;
        @(posedge clk);

        // Start second request while first is in pipeline
        a_m_addr = 19'h20000;
        @(posedge clk);

        // Start third request
        a_m_addr = 19'h30000;
        @(posedge clk);

        a_m_access = 0;

        // Count acks
        ack_count = 0;
        repeat(10) begin
            @(posedge clk);
            if (a_m_ack) ack_count++;
        end

        check_result("Pipeline processes multiple requests", ack_count == 3);

        // ================================================================
        // TEST 13: Sustained Mixed Traffic
        // ================================================================
        $display("\n--- Test 13: Sustained Mixed Traffic ---");

        a_reqs = 0;
        b_reqs = 0;
        c_reqs = 0;
        a_acks = 0;
        b_acks = 0;
        c_acks = 0;

        for (int i = 0; i < 30; i++) begin
            // Staggered access pattern
            a_m_access = (i % 5 == 0);
            b_m_access = (i % 3 == 0);
            c_m_access = (i % 4 == 0);

            if (a_m_access) a_reqs++;
            if (b_m_access) b_reqs++;
            if (c_m_access) c_reqs++;

            @(posedge clk);

            if (a_m_ack) a_acks++;
            if (b_m_ack) b_acks++;
            if (c_m_ack) c_acks++;
        end

        a_m_access = 0;
        b_m_access = 0;
        c_m_access = 0;
        repeat(10) @(posedge clk);

        // Count final acks
        for (int i = 0; i < 5; i++) begin
            if (a_m_ack) a_acks++;
            if (b_m_ack) b_acks++;
            if (c_m_ack) c_acks++;
            @(posedge clk);
        end

        $display("INFO: A-bus: %0d reqs, %0d acks | B-bus: %0d reqs, %0d acks | C-bus: %0d reqs, %0d acks",
                 a_reqs, a_acks, b_reqs, b_acks, c_reqs, c_acks);
        check_result("All buses receive service",
                     (a_acks > 0) && (b_acks > 0) && (c_acks > 0));

        // ================================================================
        // TEST 14: Grant Signal Consistency
        // ================================================================
        $display("\n--- Test 14: Grant Signal Consistency ---");

        b_m_addr = 19'hEEEEE;
        b_m_access = 1;
        repeat(5) @(posedge clk);

        observed_grant = q_grant;

        @(posedge clk);
        check_result("Grant signal stable during transaction",
                     q_grant == observed_grant);
        check_result("Ack matches grant",
                     b_m_ack && (q_grant == 2'b10));

        b_m_access = 0;
        repeat(3) @(posedge clk);

        // ================================================================
        // TEST 15: No Spurious Acks
        // ================================================================
        $display("\n--- Test 15: No Spurious Acks ---");

        a_m_access = 0;
        b_m_access = 0;
        c_m_access = 0;
        repeat(10) @(posedge clk);

        check_result("No A-bus ack when idle", !a_m_ack);
        check_result("No B-bus ack when idle", !b_m_ack);
        check_result("No C-bus ack when idle", !c_m_ack);

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
        #200000;  // 200us timeout
        $display("\n[ERROR] Testbench timeout!");
        $finish(1);
    end

endmodule
