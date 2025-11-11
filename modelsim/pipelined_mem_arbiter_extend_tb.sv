// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// Pipelined MemArbiterExtend Testbench
// Tests CPU+DMA vs VGA arbitration with fairness and priority
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module pipelined_mem_arbiter_extend_tb;

// Clock and reset
reg clk;
reg reset;

// CPU+DMA bus
reg  [19:1] cpu_m_addr;
wire [15:0] cpu_m_data_in;
reg  [15:0] cpu_m_data_out;
reg         cpu_m_access;
wire        cpu_m_ack;
reg         cpu_m_wr_en;
reg  [1:0]  cpu_m_bytesel;

// VGA bus
reg  [19:1] mcga_m_addr;
wire [15:0] mcga_m_data_in;
reg  [15:0] mcga_m_data_out;
reg         mcga_m_access;
wire        mcga_m_ack;
reg         mcga_m_wr_en;
reg  [1:0]  mcga_m_bytesel;

// VGA priority hint
reg vga_active_display;

// SDRAM interface
wire [19:1] sdram_m_addr;
reg  [15:0] sdram_m_data_in;
wire [15:0] sdram_m_data_out;
wire        sdram_m_access;
reg         sdram_m_ack;
wire        sdram_m_wr_en;
wire [1:0]  sdram_m_bytesel;
wire        q_b;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;
string test_name;

// Performance tracking
integer cycle_count;
integer cpu_requests;
integer vga_requests;
integer cpu_acks;
integer vga_acks;
integer conflicts;
integer vga_priority_wins;

// Memory model
reg [15:0] memory [0:524287];
integer mem_latency;

// DUT instantiation
PipelinedMemArbiterExtend dut (
    .clk(clk),
    .reset(reset),
    // CPU bus
    .cpu_m_addr(cpu_m_addr),
    .cpu_m_data_in(cpu_m_data_in),
    .cpu_m_data_out(cpu_m_data_out),
    .cpu_m_access(cpu_m_access),
    .cpu_m_ack(cpu_m_ack),
    .cpu_m_wr_en(cpu_m_wr_en),
    .cpu_m_bytesel(cpu_m_bytesel),
    // VGA bus
    .mcga_m_addr(mcga_m_addr),
    .mcga_m_data_in(mcga_m_data_in),
    .mcga_m_data_out(mcga_m_data_out),
    .mcga_m_access(mcga_m_access),
    .mcga_m_ack(mcga_m_ack),
    .mcga_m_wr_en(mcga_m_wr_en),
    .mcga_m_bytesel(mcga_m_bytesel),
    // Priority hint
    .vga_active_display(vga_active_display),
    // SDRAM
    .sdram_m_addr(sdram_m_addr),
    .sdram_m_data_in(sdram_m_data_in),
    .sdram_m_data_out(sdram_m_data_out),
    .sdram_m_access(sdram_m_access),
    .sdram_m_ack(sdram_m_ack),
    .sdram_m_wr_en(sdram_m_wr_en),
    .sdram_m_bytesel(sdram_m_bytesel),
    .q_b(q_b)
);

// Clock generation
initial begin
    clk = 0;
    forever #10 clk = ~clk;
end

// Memory model
always @(posedge clk) begin
    if (reset) begin
        sdram_m_ack <= 1'b0;
    end else if (sdram_m_access && !sdram_m_ack) begin
        repeat(mem_latency-1) @(posedge clk);
        sdram_m_ack <= 1'b1;
        if (sdram_m_wr_en) begin
            memory[sdram_m_addr] <= sdram_m_data_out;
        end else begin
            sdram_m_data_in <= memory[sdram_m_addr];
        end
        @(posedge clk);
        sdram_m_ack <= 1'b0;
    end else begin
        sdram_m_ack <= 1'b0;
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

// CPU transaction
task cpu_transaction(input [19:1] addr, input [15:0] data, input wr);
begin
    cpu_m_addr = addr;
    cpu_m_data_out = data;
    cpu_m_wr_en = wr;
    cpu_m_bytesel = 2'b11;
    cpu_m_access = 1'b1;
    cpu_requests = cpu_requests + 1;

    @(posedge clk);
    while (!cpu_m_ack) @(posedge clk);

    cpu_acks = cpu_acks + 1;
    cpu_m_access = 1'b0;
    @(posedge clk);
end
endtask

// VGA transaction
task vga_transaction(input [19:1] addr, input [15:0] data, input wr);
begin
    mcga_m_addr = addr;
    mcga_m_data_out = data;
    mcga_m_wr_en = wr;
    mcga_m_bytesel = 2'b11;
    mcga_m_access = 1'b1;
    vga_requests = vga_requests + 1;

    @(posedge clk);
    while (!mcga_m_ack) @(posedge clk);

    vga_acks = vga_acks + 1;
    mcga_m_access = 1'b0;
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

// Conflict detector
always @(posedge clk) begin
    if (!reset && cpu_m_access && mcga_m_access) begin
        conflicts <= conflicts + 1;
        if (mcga_m_ack && !cpu_m_ack && vga_active_display)
            vga_priority_wins <= vga_priority_wins + 1;
    end
end

// Main test sequence
initial begin
    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    cycle_count = 0;
    cpu_requests = 0;
    vga_requests = 0;
    cpu_acks = 0;
    vga_acks = 0;
    conflicts = 0;
    vga_priority_wins = 0;

    reset = 1;
    cpu_m_access = 0;
    mcga_m_access = 0;
    cpu_m_wr_en = 0;
    mcga_m_wr_en = 0;
    vga_active_display = 0;
    mem_latency = 2;

    $display("========================================");
    $display("Pipelined MemArbiterExtend Testbench");
    $display("========================================");

    init_memory();

    #100;
    reset = 0;
    #40;

    //==================================================================
    // Test 1: Basic CPU Access
    //==================================================================
    test_name = "Basic CPU read";
    $display("\n--- Test 1: %s ---", test_name);
    begin
        cpu_transaction(19'h01000, 16'h0000, 1'b0);
        check_result(cpu_m_ack && cpu_m_data_in == (16'h1000 ^ 16'hA5A5),
                    "CPU read returns correct data");
    end

    //==================================================================
    // Test 2: Basic VGA Access
    //==================================================================
    test_name = "Basic VGA read";
    $display("\n--- Test 2: %s ---", test_name);
    begin
        vga_transaction(19'h02000, 16'h0000, 1'b0);
        check_result(mcga_m_ack && mcga_m_data_in == (16'h2000 ^ 16'hA5A5),
                    "VGA read returns correct data");
    end

    //==================================================================
    // Test 3: VGA Priority During Active Display
    //==================================================================
    test_name = "VGA priority during active display";
    $display("\n--- Test 3: %s ---", test_name);
    begin
        vga_active_display = 1'b1;

        // Both request simultaneously
        cpu_m_addr = 19'h03000;
        cpu_m_data_out = 16'h0000;
        cpu_m_wr_en = 1'b0;
        cpu_m_bytesel = 2'b11;
        cpu_m_access = 1'b1;

        mcga_m_addr = 19'h04000;
        mcga_m_data_out = 16'h0000;
        mcga_m_wr_en = 1'b0;
        mcga_m_bytesel = 2'b11;
        mcga_m_access = 1'b1;

        @(posedge clk);

        // VGA should be granted first
        wait(mcga_m_ack);
        check_result(mcga_m_ack && !cpu_m_ack,
                    "VGA served first during active display");

        wait(cpu_m_ack);
        check_result(cpu_m_ack,
                    "CPU served after VGA");

        cpu_m_access = 1'b0;
        mcga_m_access = 1'b0;
        vga_active_display = 1'b0;
        @(posedge clk);
    end

    //==================================================================
    // Test 4: Round-Robin During Blanking
    //==================================================================
    test_name = "Round-robin fairness during blanking";
    $display("\n--- Test 4: %s ---", test_name);
    begin
        integer i;
        integer vga_first_count;
        integer cpu_first_count;

        vga_active_display = 1'b0;  // Blanking period
        vga_first_count = 0;
        cpu_first_count = 0;

        // Multiple simultaneous requests
        for (i = 0; i < 10; i = i + 1) begin
            // Start both requests
            cpu_m_addr = 19'h05000 + i;
            cpu_m_data_out = 16'h0000;
            cpu_m_wr_en = 1'b0;
            cpu_m_bytesel = 2'b11;
            cpu_m_access = 1'b1;

            mcga_m_addr = 19'h06000 + i;
            mcga_m_data_out = 16'h0000;
            mcga_m_wr_en = 1'b0;
            mcga_m_bytesel = 2'b11;
            mcga_m_access = 1'b1;

            @(posedge clk);

            // Check who gets served first
            if (mcga_m_ack)
                vga_first_count = vga_first_count + 1;
            else if (cpu_m_ack)
                cpu_first_count = cpu_first_count + 1;

            wait(cpu_m_ack && mcga_m_ack);
            cpu_m_access = 1'b0;
            mcga_m_access = 1'b0;
            @(posedge clk);
        end

        $display("  VGA served first: %0d times", vga_first_count);
        $display("  CPU served first: %0d times", cpu_first_count);

        check_result(vga_first_count >= 3 && cpu_first_count >= 3,
                    "Round-robin fairness (both served fairly)");
    end

    //==================================================================
    // Test 5: Starvation Prevention
    //==================================================================
    test_name = "CPU starvation prevention";
    $display("\n--- Test 5: %s ---", test_name);
    begin
        integer i;

        vga_active_display = 1'b1;  // VGA has priority

        // VGA makes many requests
        for (i = 0; i < 15; i = i + 1) begin
            vga_transaction(19'h07000 + i, 16'h0000, 1'b0);
        end

        // Now both request - CPU should get priority due to age
        cpu_m_addr = 19'h08000;
        cpu_m_data_out = 16'h0000;
        cpu_m_wr_en = 1'b0;
        cpu_m_bytesel = 2'b11;
        cpu_m_access = 1'b1;

        mcga_m_addr = 19'h09000;
        mcga_m_data_out = 16'h0000;
        mcga_m_wr_en = 1'b0;
        mcga_m_bytesel = 2'b11;
        mcga_m_access = 1'b1;

        @(posedge clk);

        // CPU should be granted first due to age > 12
        wait(cpu_m_ack || mcga_m_ack);
        check_result(cpu_m_ack,
                    "CPU granted despite VGA priority (starvation prevention)");

        cpu_m_access = 1'b0;
        mcga_m_access = 1'b0;
        vga_active_display = 1'b0;
        @(posedge clk);
    end

    //==================================================================
    // Test 6: Back-to-Back Performance
    //==================================================================
    test_name = "Back-to-back throughput";
    $display("\n--- Test 6: %s ---", test_name);
    begin
        integer start_cycle, end_cycle;
        integer i;
        real throughput;

        start_cycle = cycle_count;

        for (i = 0; i < 20; i = i + 1) begin
            if (i[0])
                vga_transaction(19'h10000 + i, 16'h0000, 1'b0);
            else
                cpu_transaction(19'h11000 + i, 16'h0000, 1'b0);
        end

        end_cycle = cycle_count;

        throughput = real'(20) / real'(end_cycle - start_cycle);

        $display("  20 operations in %0d cycles", end_cycle - start_cycle);
        $display("  Throughput: %.3f ops/cycle", throughput);

        check_result(throughput >= 0.80,
                    $sformatf("Throughput %.3f >= 0.80", throughput));
    end

    //==================================================================
    // Test 7: Write Operations
    //==================================================================
    test_name = "Write operations";
    $display("\n--- Test 7: %s ---", test_name);
    begin
        cpu_transaction(19'h12000, 16'hCDAB, 1'b1);
        vga_transaction(19'h13000, 16'h1234, 1'b1);

        cpu_transaction(19'h12000, 16'h0000, 1'b0);
        check_result(cpu_m_data_in == 16'hCDAB,
                    "CPU write verified");

        vga_transaction(19'h13000, 16'h0000, 1'b0);
        check_result(mcga_m_data_in == 16'h1234,
                    "VGA write verified");
    end

    //==================================================================
    // Test 8: Sustained Mixed Load
    //==================================================================
    test_name = "Sustained mixed load (100 ops)";
    $display("\n--- Test 8: %s ---", test_name);
    begin
        integer start_cycle, end_cycle;
        integer i;
        real throughput;

        start_cycle = cycle_count;
        vga_active_display = 1'b1;

        for (i = 0; i < 100; i = i + 1) begin
            if (i[1:0] == 0)
                vga_transaction(19'h20000 + i, 16'h0000, 1'b0);
            else
                cpu_transaction(19'h21000 + i, 16'h0000, 1'b0);
        end

        end_cycle = cycle_count;

        throughput = real'(100) / real'(end_cycle - start_cycle);

        $display("  100 operations in %0d cycles", end_cycle - start_cycle);
        $display("  Throughput: %.3f ops/cycle", throughput);
        $display("  Target: >= 0.85 ops/cycle");

        check_result(throughput >= 0.85,
                    $sformatf("Sustained throughput %.3f >= 0.85", throughput));

        vga_active_display = 1'b0;
    end

    //==================================================================
    // Performance Summary
    //==================================================================
    #1000;

    $display("\n========================================");
    $display("Performance Summary:");
    $display("  Total cycles: %0d", cycle_count);
    $display("  CPU requests: %0d", cpu_requests);
    $display("  VGA requests: %0d", vga_requests);
    $display("  CPU acks: %0d", cpu_acks);
    $display("  VGA acks: %0d", vga_acks);
    $display("  Conflicts: %0d", conflicts);
    $display("  VGA priority wins: %0d", vga_priority_wins);
    $display("  Overall throughput: %.3f ops/cycle",
            real'(cpu_acks + vga_acks) / real'(cycle_count));
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
    #500000;
    $display("\n========================================");
    $display("ERROR: Simulation timeout!");
    $display("========================================");
    $finish(2);
end

// Waveform dump
initial begin
    $dumpfile("pipelined_mem_arbiter_extend_tb.vcd");
    $dumpvars(0, pipelined_mem_arbiter_extend_tb);
end

endmodule
`default_nettype wire
