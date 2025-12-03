// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// Pipelined DMA Arbiter Testbench
// Comprehensive verification of pipelined arbitration performance
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module pipelined_dma_arbiter_tb;

// Clock and reset
reg clk;
reg reset;

// DMA bus (A-bus)
reg  [19:1] a_m_addr;
wire [15:0] a_m_data_in;
reg  [15:0] a_m_data_out;
reg         a_m_access;
wire        a_m_ack;
reg         a_m_wr_en;
reg  [1:0]  a_m_bytesel;
reg         ioa;

// CPU Data bus (B-bus)
reg  [19:1] b_m_addr;
wire [15:0] b_m_data_in;
reg  [15:0] b_m_data_out;
reg         b_m_access;
wire        b_m_ack;
reg         b_m_wr_en;
reg  [1:0]  b_m_bytesel;
reg         iob;

// Output bus
wire [19:1] q_m_addr;
reg  [15:0] q_m_data_in;
wire [15:0] q_m_data_out;
wire        q_m_access;
reg         q_m_ack;
wire        q_m_wr_en;
wire [1:0]  q_m_bytesel;
wire        ioq;
wire        q_b;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;
string test_name;

// Performance tracking
integer cycle_count;
integer a_requests;
integer b_requests;
integer a_acks;
integer b_acks;
integer total_latency_a;
integer total_latency_b;
integer request_time_a;
integer request_time_b;

// Memory model
reg [15:0] memory [0:524287];
integer mem_latency;

// DUT instantiation
PipelinedDMAArbiter dut (
    .clk(clk),
    .reset(reset),
    // A-bus
    .a_m_addr(a_m_addr),
    .a_m_data_in(a_m_data_in),
    .a_m_data_out(a_m_data_out),
    .a_m_access(a_m_access),
    .a_m_ack(a_m_ack),
    .a_m_wr_en(a_m_wr_en),
    .a_m_bytesel(a_m_bytesel),
    .ioa(ioa),
    // B-bus
    .b_m_addr(b_m_addr),
    .b_m_data_in(b_m_data_in),
    .b_m_data_out(b_m_data_out),
    .b_m_access(b_m_access),
    .b_m_ack(b_m_ack),
    .b_m_wr_en(b_m_wr_en),
    .b_m_bytesel(b_m_bytesel),
    .iob(iob),
    // Output
    .q_m_addr(q_m_addr),
    .q_m_data_in(q_m_data_in),
    .q_m_data_out(q_m_data_out),
    .q_m_access(q_m_access),
    .q_m_ack(q_m_ack),
    .q_m_wr_en(q_m_wr_en),
    .q_m_bytesel(q_m_bytesel),
    .ioq(ioq),
    .q_b(q_b)
);

// Clock generation: 50 MHz
initial begin
    clk = 0;
    forever #10 clk = ~clk;
end

// Memory model with configurable latency - state machine based
reg [3:0] mem_state;
reg [3:0] mem_wait_count;
localparam MEM_IDLE = 0;
localparam MEM_WAIT = 1;
localparam MEM_ACK = 2;

always @(posedge clk) begin
    if (reset) begin
        q_m_ack <= 1'b0;
        q_m_data_in <= 16'h0;
        mem_state <= MEM_IDLE;
        mem_wait_count <= 0;
    end else begin
        case (mem_state)
            MEM_IDLE: begin
                q_m_ack <= 1'b0;
                if (q_m_access) begin
                    if (mem_latency <= 1) begin
                        // Immediate response
                        q_m_ack <= 1'b1;
                        if (!q_m_wr_en) begin
                            q_m_data_in <= memory[q_m_addr];
                        end else begin
                            memory[q_m_addr] <= q_m_data_out;
                        end
                        mem_state <= MEM_ACK;
                    end else begin
                        // Wait for latency
                        mem_wait_count <= mem_latency - 1;
                        mem_state <= MEM_WAIT;
                    end
                end
            end
            MEM_WAIT: begin
                q_m_ack <= 1'b0;
                if (mem_wait_count > 1) begin
                    mem_wait_count <= mem_wait_count - 1;
                end else begin
                    // Assert ack and provide/capture data
                    q_m_ack <= 1'b1;
                    if (!q_m_wr_en) begin
                        q_m_data_in <= memory[q_m_addr];
                    end else begin
                        memory[q_m_addr] <= q_m_data_out;
                    end
                    mem_state <= MEM_ACK;
                end
            end
            MEM_ACK: begin
                // Deassert ack and return to idle
                q_m_ack <= 1'b0;
                mem_state <= MEM_IDLE;
            end
            default: mem_state <= MEM_IDLE;
        endcase
    end
end

// Initialize memory
task init_memory();
    integer i;
begin
    for (i = 0; i < 524288; i = i + 1) begin
        memory[i] = i[15:0] ^ 16'hA5A5;
    end
end
endtask

// Variables to capture data from transactions
reg [15:0] a_last_data_in;
reg [15:0] b_last_data_in;
reg a_last_ack;
reg b_last_ack;

// A-bus transaction - captures data when ack received
task a_transaction(input [19:1] addr, input [15:0] data, input wr, input [1:0] bytesel);
    integer start_time;
    integer timeout;
begin
    start_time = cycle_count;
    a_m_addr = addr;
    a_m_data_out = data;
    a_m_wr_en = wr;
    a_m_bytesel = bytesel;
    a_m_access = 1'b1;
    ioa = 1'b0;
    a_requests = a_requests + 1;
    request_time_a = cycle_count;

    timeout = 0;
    @(posedge clk);
    while (!a_m_ack && timeout < 50) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    if (a_m_ack) begin
        // Capture data while ack is still high
        a_last_data_in = a_m_data_in;
        a_last_ack = 1'b1;
        a_acks = a_acks + 1;
        total_latency_a = total_latency_a + (cycle_count - start_time);
    end else begin
        a_last_ack = 1'b0;
        $display("[WARN] A-bus transaction timeout at addr 0x%05x", addr);
    end

    a_m_access = 1'b0;
    @(posedge clk);
end
endtask

// B-bus transaction - captures data when ack received
task b_transaction(input [19:1] addr, input [15:0] data, input wr, input [1:0] bytesel);
    integer start_time;
    integer timeout;
begin
    start_time = cycle_count;
    b_m_addr = addr;
    b_m_data_out = data;
    b_m_wr_en = wr;
    b_m_bytesel = bytesel;
    b_m_access = 1'b1;
    iob = 1'b0;
    b_requests = b_requests + 1;
    request_time_b = cycle_count;

    timeout = 0;
    @(posedge clk);
    while (!b_m_ack && timeout < 50) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    if (b_m_ack) begin
        // Capture data while ack is still high
        b_last_data_in = b_m_data_in;
        b_last_ack = 1'b1;
        b_acks = b_acks + 1;
        total_latency_b = total_latency_b + (cycle_count - start_time);
    end else begin
        b_last_ack = 1'b0;
        $display("[WARN] B-bus transaction timeout at addr 0x%05x", addr);
    end

    b_m_access = 1'b0;
    @(posedge clk);
end
endtask

// Check test result
task check_result(input condition, input string description);
begin
    test_count = test_count + 1;
    if (condition) begin
        pass_count = pass_count + 1;
        $display("[PASS] Test %0d: %s", test_count, description);
    end else begin
        fail_count = fail_count + 1;
        $display("[FAIL] Test %0d: %s", test_count, description);
    end
end
endtask

// Cycle counter
always @(posedge clk) begin
    if (!reset) cycle_count <= cycle_count + 1;
end

// Main test sequence
initial begin
    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    cycle_count = 0;
    a_requests = 0;
    b_requests = 0;
    a_acks = 0;
    b_acks = 0;
    total_latency_a = 0;
    total_latency_b = 0;

    reset = 1;
    a_m_access = 0;
    b_m_access = 0;
    a_m_wr_en = 0;
    b_m_wr_en = 0;
    mem_latency = 2;  // 2 cycle memory

    $display("========================================");
    $display("Pipelined DMA Arbiter Testbench");
    $display("========================================");

    init_memory();

    #100;
    reset = 0;
    #40;

    //==================================================================
    // Test 1: Basic A-bus Access
    //==================================================================
    test_name = "Basic A-bus read";
    $display("\n--- Test 1: %s ---", test_name);
    begin
        integer start_cycle;
        reg [15:0] expected_data;
        start_cycle = cycle_count;

        a_transaction(19'h01000, 16'h0000, 1'b0, 2'b11);

        expected_data = 16'h1000 ^ 16'hA5A5;
        $display("  A-bus read: got 0x%04x, expected 0x%04x", a_last_data_in, expected_data);
        check_result(a_last_ack && a_last_data_in == expected_data,
                    "A-bus read returns correct data");
        // 4-stage pipeline + 2-cycle memory = ~6-8 cycles
        check_result((cycle_count - start_cycle) <= 10,
                    $sformatf("A-bus latency %0d <= 10 cycles", cycle_count - start_cycle));
    end

    //==================================================================
    // Test 2: Basic B-bus Access (Higher Priority)
    //==================================================================
    test_name = "Basic B-bus read";
    $display("\n--- Test 2: %s ---", test_name);
    begin
        integer start_cycle;
        reg [15:0] expected_data;
        start_cycle = cycle_count;

        b_transaction(19'h02000, 16'h0000, 1'b0, 2'b11);

        expected_data = 16'h2000 ^ 16'hA5A5;
        $display("  B-bus read: got 0x%04x, expected 0x%04x", b_last_data_in, expected_data);
        check_result(b_last_ack && b_last_data_in == expected_data,
                    "B-bus read returns correct data");
        // 4-stage pipeline + 2-cycle memory = ~6-8 cycles
        check_result((cycle_count - start_cycle) <= 10,
                    $sformatf("B-bus latency %0d <= 10 cycles", cycle_count - start_cycle));
    end

    //==================================================================
    // Test 3: B-bus Priority (Both Request Simultaneously)
    //==================================================================
    test_name = "B-bus priority test";
    $display("\n--- Test 3: %s ---", test_name);
    begin
        integer timeout;

        a_m_addr = 19'h03000;
        a_m_data_out = 16'h0000;
        a_m_wr_en = 1'b0;
        a_m_bytesel = 2'b11;
        a_m_access = 1'b1;
        ioa = 1'b0;

        b_m_addr = 19'h04000;
        b_m_data_out = 16'h0000;
        b_m_wr_en = 1'b0;
        b_m_bytesel = 2'b11;
        b_m_access = 1'b1;
        iob = 1'b0;

        @(posedge clk);

        // B should be granted first - wait with timeout
        timeout = 0;
        while (!b_m_ack && timeout < 50) begin
            @(posedge clk);
            timeout = timeout + 1;
        end
        check_result(b_m_ack && !a_m_ack,
                    "B-bus served first when both request");

        // Deassert B-bus access immediately after its ack
        b_m_access = 1'b0;
        @(posedge clk);

        // Now wait for A-bus ack with timeout
        timeout = 0;
        while (!a_m_ack && timeout < 50) begin
            @(posedge clk);
            timeout = timeout + 1;
        end
        check_result(a_m_ack,
                    "A-bus served after B-bus");

        a_m_access = 1'b0;
        @(posedge clk);
    end

    //==================================================================
    // Test 4: Back-to-Back Requests (Pipeline Test)
    //==================================================================
    test_name = "Back-to-back pipeline performance";
    $display("\n--- Test 4: %s ---", test_name);
    begin
        integer start_cycle, end_cycle;
        integer i;

        start_cycle = cycle_count;

        // Issue 10 B-bus requests back-to-back
        for (i = 0; i < 10; i = i + 1) begin
            b_transaction(19'h05000 + i, 16'h0000, 1'b0, 2'b11);
        end

        end_cycle = cycle_count;

        // With 4-stage pipeline + 2-cycle memory, first request ~6 cycles, subsequent ~4 cycles
        // 10 requests: ~6 + 9*4 = ~42 cycles, allow up to 100 for margin
        check_result((end_cycle - start_cycle) <= 100,
                    $sformatf("10 requests in %0d cycles (target: <=100)",
                             end_cycle - start_cycle));

        // Calculate throughput
        $display("  Throughput: %.2f ops/cycle",
                real'(10) / real'(end_cycle - start_cycle));
    end

    //==================================================================
    // Test 5: Interleaved A/B Requests
    //==================================================================
    test_name = "Interleaved A/B requests";
    $display("\n--- Test 5: %s ---", test_name);
    begin
        integer i;

        for (i = 0; i < 8; i = i + 1) begin
            b_transaction(19'h06000 + i, 16'h0000, 1'b0, 2'b11);
            a_transaction(19'h07000 + i, 16'h0000, 1'b0, 2'b11);
        end

        check_result(a_acks >= 8 && b_acks >= 18,
                    "All interleaved requests completed");
    end

    //==================================================================
    // Test 6: Write Operations
    //==================================================================
    test_name = "Write operations";
    $display("\n--- Test 6: %s ---", test_name);
    begin
        // Write via A-bus
        a_transaction(19'h08000, 16'hDEAD, 1'b1, 2'b11);

        // Write via B-bus
        b_transaction(19'h09000, 16'hBEEF, 1'b1, 2'b11);

        // Read back
        a_transaction(19'h08000, 16'h0000, 1'b0, 2'b11);
        $display("  A-bus write verify: got 0x%04x, expected 0xDEAD", a_last_data_in);
        check_result(a_last_data_in == 16'hDEAD,
                    "A-bus write verified");

        b_transaction(19'h09000, 16'h0000, 1'b0, 2'b11);
        $display("  B-bus write verify: got 0x%04x, expected 0xBEEF", b_last_data_in);
        check_result(b_last_data_in == 16'hBEEF,
                    "B-bus write verified");
    end

    //==================================================================
    // Test 7: Sustained Throughput Test
    //==================================================================
    test_name = "Sustained throughput (100 ops)";
    $display("\n--- Test 7: %s ---", test_name);
    begin
        integer start_cycle, end_cycle;
        integer i;
        real throughput;

        start_cycle = cycle_count;

        for (i = 0; i < 100; i = i + 1) begin
            if (i[0])
                b_transaction(19'h10000 + i, 16'h0000, 1'b0, 2'b11);
            else
                a_transaction(19'h10000 + i, 16'h0000, 1'b0, 2'b11);
        end

        end_cycle = cycle_count;

        throughput = real'(100) / real'(end_cycle - start_cycle);

        $display("  100 operations in %0d cycles", end_cycle - start_cycle);
        $display("  Throughput: %.3f ops/cycle", throughput);
        $display("  Target: >= 0.10 ops/cycle (pipeline + memory latency)");

        // With sequential transactions and pipeline, throughput is limited
        check_result(throughput >= 0.10,
                    $sformatf("Sustained throughput %.3f >= 0.10", throughput));
    end

    //==================================================================
    // Test 8: Latency Measurement
    //==================================================================
    test_name = "Average latency measurement";
    $display("\n--- Test 8: %s ---", test_name);
    begin
        real avg_latency_a, avg_latency_b;

        avg_latency_a = real'(total_latency_a) / real'(a_acks);
        avg_latency_b = real'(total_latency_b) / real'(b_acks);

        $display("  A-bus average latency: %.2f cycles", avg_latency_a);
        $display("  B-bus average latency: %.2f cycles", avg_latency_b);
        $display("  Target: <= 10.0 cycles (4-stage pipeline + memory)");

        // 4-stage pipeline + 2-cycle memory = ~6-8 cycles minimum
        check_result(avg_latency_a <= 10.0 && avg_latency_b <= 10.0,
                    "Average latency <= 10 cycles");
    end

    //==================================================================
    // Performance Summary
    //==================================================================
    #1000;

    $display("\n========================================");
    $display("Performance Summary:");
    $display("  Total cycles: %0d", cycle_count);
    $display("  A-bus requests: %0d", a_requests);
    $display("  B-bus requests: %0d", b_requests);
    $display("  A-bus acks: %0d", a_acks);
    $display("  B-bus acks: %0d", b_acks);
    $display("  Overall throughput: %.3f ops/cycle",
            real'(a_acks + b_acks) / real'(cycle_count));
    $display("========================================");

    $display("\n========================================");
    $display("Test Results:");
    $display("  Total: %0d", test_count);
    $display("  Pass:  %0d", pass_count);
    $display("  Fail:  %0d", fail_count);
    $display("========================================");

    if (fail_count == 0) begin
        $display("*** ALL TESTS PASSED ***");
        $finish(0);
    end else begin
        $display("*** SOME TESTS FAILED ***");
        $finish(1);
    end
end

// Timeout watchdog
initial begin
    #5000000;  // 5ms timeout for all tests
    $display("\n========================================");
    $display("ERROR: Simulation timeout!");
    $display("========================================");
    $finish(2);
end

// Waveform dump
initial begin
    $dumpfile("pipelined_dma_arbiter_tb.vcd");
    $dumpvars(0, pipelined_dma_arbiter_tb);
end

endmodule
`default_nettype wire
