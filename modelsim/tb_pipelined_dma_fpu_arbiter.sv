// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// Testbench for PipelinedDMAFPUArbiter
//
// Tests:
// 1. Priority arbitration (DMA > FPU > CPU)
// 2. Data routing correctness
// 3. ACK signal generation
// 4. Pipelined operation
// 5. Simultaneous access scenarios
// 6. Read and write operations

`timescale 1ns / 1ps

module tb_pipelined_dma_fpu_arbiter;

    // Clock and reset
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

    // Output bus (simulated memory)
    logic [19:1] q_m_addr;
    logic [15:0] q_m_data_in;
    logic [15:0] q_m_data_out;
    logic q_m_access;
    logic q_m_ack;
    logic q_m_wr_en;
    logic [1:0] q_m_bytesel;
    logic ioq;
    logic [1:0] q_grant;

    // Test tracking
    integer test_count;
    integer pass_count;
    integer fail_count;

    // Simulated memory
    logic [15:0] memory [0:1023];  // 2KB test memory
    integer i;

    // Instantiate arbiter
    PipelinedDMAFPUArbiter dut (
        .clk(clk),
        .reset(reset),

        // DMA bus (A)
        .a_m_addr(a_m_addr),
        .a_m_data_in(a_m_data_in),
        .a_m_data_out(a_m_data_out),
        .a_m_access(a_m_access),
        .a_m_ack(a_m_ack),
        .a_m_wr_en(a_m_wr_en),
        .a_m_bytesel(a_m_bytesel),
        .ioa(ioa),

        // CPU bus (B)
        .b_m_addr(b_m_addr),
        .b_m_data_in(b_m_data_in),
        .b_m_data_out(b_m_data_out),
        .b_m_access(b_m_access),
        .b_m_ack(b_m_ack),
        .b_m_wr_en(b_m_wr_en),
        .b_m_bytesel(b_m_bytesel),
        .iob(iob),

        // FPU bus (C)
        .c_m_addr(c_m_addr),
        .c_m_data_in(c_m_data_in),
        .c_m_data_out(c_m_data_out),
        .c_m_access(c_m_access),
        .c_m_ack(c_m_ack),
        .c_m_wr_en(c_m_wr_en),
        .c_m_bytesel(c_m_bytesel),

        // Output
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

    // Clock generation (50 MHz)
    initial begin
        clk = 0;
        forever #10 clk = ~clk;  // 20ns period = 50 MHz
    end

    // Simulated memory response
    always @(posedge clk) begin
        if (reset) begin
            q_m_ack <= 1'b0;
            q_m_data_in <= 16'h0;
        end else begin
            // Acknowledge access on next cycle (simple memory model)
            q_m_ack <= q_m_access;

            // Handle memory read
            if (q_m_access && !q_m_wr_en) begin
                q_m_data_in <= memory[q_m_addr[10:1]];  // Use lower 10 bits as index
            end

            // Handle memory write
            if (q_m_access && q_m_wr_en) begin
                memory[q_m_addr[10:1]] <= q_m_data_out;
            end
        end
    end

    // Test procedure
    initial begin
        $display("========================================");
        $display("PipelinedDMAFPUArbiter Integration Test");
        $display("========================================");

        // Initialize
        test_count = 0;
        pass_count = 0;
        fail_count = 0;

        // Initialize memory
        for (i = 0; i < 1024; i = i + 1) begin
            memory[i] = i[15:0];  // Memory[i] = i
        end

        // Initialize signals
        reset = 1;
        a_m_addr = 19'h0;
        a_m_data_out = 16'h0;
        a_m_access = 0;
        a_m_wr_en = 0;
        a_m_bytesel = 2'b11;
        ioa = 0;

        b_m_addr = 19'h0;
        b_m_data_out = 16'h0;
        b_m_access = 0;
        b_m_wr_en = 0;
        b_m_bytesel = 2'b11;
        iob = 0;

        c_m_addr = 19'h0;
        c_m_data_out = 16'h0;
        c_m_access = 0;
        c_m_wr_en = 0;
        c_m_bytesel = 2'b11;

        // Release reset
        #100;
        reset = 0;
        #40;

        //======================================================================
        // TEST 1: CPU-only access (B-bus)
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: CPU-only memory read (B-bus)", test_count);

        @(posedge clk);
        b_m_addr = 19'h0005;  // Word address 5 (memory[5])
        b_m_access = 1;
        b_m_wr_en = 0;

        // Wait for acknowledge
        wait(b_m_ack);
        @(posedge clk);
        b_m_access = 0;

        @(posedge clk);
        if (b_m_data_in == 16'h0005) begin
            $display("  PASS: CPU read correct data = 0x%04X", b_m_data_in);
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected 0x0005, got 0x%04X", b_m_data_in);
            fail_count = fail_count + 1;
        end

        @(posedge clk);
        @(posedge clk);

        //======================================================================
        // TEST 2: FPU-only access (C-bus)
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: FPU-only memory read (C-bus)", test_count);

        @(posedge clk);
        c_m_addr = 19'h000A;  // Word address 10 (memory[10])
        c_m_access = 1;
        c_m_wr_en = 0;

        // Wait for acknowledge
        wait(c_m_ack);
        @(posedge clk);
        c_m_access = 0;

        @(posedge clk);
        if (c_m_data_in == 16'h000A) begin
            $display("  PASS: FPU read correct data = 0x%04X", c_m_data_in);
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected 0x000A, got 0x%04X", c_m_data_in);
            fail_count = fail_count + 1;
        end

        @(posedge clk);
        @(posedge clk);

        //======================================================================
        // TEST 3: DMA-only access (A-bus)
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: DMA-only memory read (A-bus)", test_count);

        @(posedge clk);
        a_m_addr = 19'h000F;  // Word address 15 (memory[15])
        a_m_access = 1;
        a_m_wr_en = 0;

        // Wait for acknowledge
        wait(a_m_ack);
        @(posedge clk);
        a_m_access = 0;

        @(posedge clk);
        if (a_m_data_in == 16'h000F) begin
            $display("  PASS: DMA read correct data = 0x%04X", a_m_data_in);
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected 0x000F, got 0x%04X", a_m_data_in);
            fail_count = fail_count + 1;
        end

        @(posedge clk);
        @(posedge clk);

        //======================================================================
        // TEST 4: FPU write operation (C-bus)
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: FPU memory write (C-bus)", test_count);

        @(posedge clk);
        c_m_addr = 19'h0014;  // Word address 20 (memory[20])
        c_m_data_out = 16'hABCD;
        c_m_access = 1;
        c_m_wr_en = 1;

        // Wait for acknowledge
        wait(c_m_ack);
        @(posedge clk);
        c_m_access = 0;
        c_m_wr_en = 0;

        @(posedge clk);
        @(posedge clk);

        // Verify write
        if (memory[20] == 16'hABCD) begin
            $display("  PASS: FPU wrote correct data to memory");
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Memory[20] = 0x%04X, expected 0xABCD", memory[20]);
            fail_count = fail_count + 1;
        end

        @(posedge clk);
        @(posedge clk);

        //======================================================================
        // TEST 5: Priority - DMA > FPU (simultaneous access)
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: DMA priority over FPU", test_count);

        @(posedge clk);
        // Both request simultaneously
        a_m_addr = 19'h0019;  // DMA word address 25 (memory[25])
        a_m_access = 1;
        c_m_addr = 19'h001E;  // FPU word address 30 (memory[30])
        c_m_access = 1;

        // DMA should win first
        wait(a_m_ack);
        if (q_grant == 2'b01) begin  // A-bus granted
            $display("  PASS: DMA won arbitration (grant = %02b)", q_grant);
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected DMA grant (01), got %02b", q_grant);
            fail_count = fail_count + 1;
        end

        @(posedge clk);
        a_m_access = 0;

        // FPU should win next
        wait(c_m_ack);
        @(posedge clk);
        c_m_access = 0;

        @(posedge clk);
        @(posedge clk);

        //======================================================================
        // TEST 6: Priority - DMA > CPU (simultaneous access)
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: DMA priority over CPU", test_count);

        @(posedge clk);
        // Both request simultaneously
        a_m_addr = 19'h0023;  // DMA word address 35 (memory[35])
        a_m_access = 1;
        b_m_addr = 19'h0028;  // CPU word address 40 (memory[40])
        b_m_access = 1;

        // DMA should win first
        wait(a_m_ack);
        if (q_grant == 2'b01) begin  // A-bus granted
            $display("  PASS: DMA won over CPU (grant = %02b)", q_grant);
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected DMA grant (01), got %02b", q_grant);
            fail_count = fail_count + 1;
        end

        @(posedge clk);
        a_m_access = 0;

        // CPU should win next
        wait(b_m_ack);
        @(posedge clk);
        b_m_access = 0;

        @(posedge clk);
        @(posedge clk);

        //======================================================================
        // TEST 7: Priority - FPU > CPU (simultaneous access)
        //======================================================================
        test_count = test_count + 1;
        $display("\nTest %0d: FPU priority over CPU", test_count);

        @(posedge clk);
        // Both request simultaneously (no DMA)
        c_m_addr = 19'h002D;  // FPU word address 45 (memory[45])
        c_m_access = 1;
        b_m_addr = 19'h0032;  // CPU word address 50 (memory[50])
        b_m_access = 1;

        // FPU should win first
        wait(c_m_ack);
        if (q_grant == 2'b11) begin  // C-bus granted
            $display("  PASS: FPU won over CPU (grant = %02b)", q_grant);
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected FPU grant (11), got %02b", q_grant);
            fail_count = fail_count + 1;
        end

        @(posedge clk);
        c_m_access = 0;

        // CPU should win next
        wait(b_m_ack);
        @(posedge clk);
        b_m_access = 0;

        @(posedge clk);
        @(posedge clk);

        //======================================================================
        // TEST 8: All three requesting (DMA > FPU > CPU priority)
        //======================================================================
        
        $display("\nTest %0d: All three buses requesting", test_count);

        @(posedge clk);
        // All three request simultaneously
        a_m_addr = 19'h0037;  // DMA word address 55 (memory[55])
        a_m_access = 1;
        c_m_addr = 19'h003C;  // FPU word address 60 (memory[60])
        c_m_access = 1;
        b_m_addr = 19'h0041;  // CPU word address 65 (memory[65])
        b_m_access = 1;

        // DMA should win first
		test_count = test_count + 1;
        wait(a_m_ack);
        if (q_grant == 2'b01) begin
            $display("  PASS: DMA won first (grant = %02b)", q_grant);
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected DMA first, got grant %02b", q_grant);
            fail_count = fail_count + 1;
        end

        @(posedge clk);
        a_m_access = 0;

        // FPU should win second
		test_count = test_count + 1;
        wait(c_m_ack);
        if (q_grant == 2'b11) begin
            $display("  PASS: FPU won second (grant = %02b)", q_grant);
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected FPU second, got grant %02b", q_grant);
            fail_count = fail_count + 1;
        end

        @(posedge clk);
        c_m_access = 0;

        // CPU should win third
		test_count = test_count + 1;
        wait(b_m_ack);
        if (q_grant == 2'b10) begin
            $display("  PASS: CPU won third (grant = %02b)", q_grant);
            pass_count = pass_count + 1;
        end else begin
            $display("  FAIL: Expected CPU third, got grant %02b", q_grant);
            fail_count = fail_count + 1;
        end

        @(posedge clk);
        b_m_access = 0;

        @(posedge clk);
        @(posedge clk);

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
        if (test_count > 0)
            $display("Pass Rate:    %0d%%", (pass_count * 100) / test_count);
        $display("========================================");

        if (fail_count == 0) begin
            $display("✓ ALL TESTS PASSED!");
            $display("PipelinedDMAFPUArbiter integration validated successfully.");
        end else begin
            $display("✗ SOME TESTS FAILED");
            $display("Please review failures above.");
        end

        $display("\n");
        $finish;
    end

    // Timeout watchdog
    initial begin
        #500000;  // 500 microseconds timeout
        $display("\n*** ERROR: Test timeout! ***");
        $finish;
    end

endmodule
