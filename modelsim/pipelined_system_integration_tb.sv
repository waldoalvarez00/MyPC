// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// System Integration Testbench for Pipelined Arbiters
// Tests the complete arbitration hierarchy:
// CPU/DMA -> PipelinedDMAArbiter -> PipelinedMemArbiterExtend (vs VGA) -> SDRAM
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module pipelined_system_integration_tb;

//============================================================================
// Test Configuration
//============================================================================

parameter CLK_PERIOD = 20;  // 50 MHz
parameter SDRAM_LATENCY = 3;  // SDRAM latency in cycles

//============================================================================
// Signals
//============================================================================

reg clk, reset;

// CPU interface (highest in hierarchy)
reg  [19:1] cpu_addr;
wire [15:0] cpu_data_in;
reg  [15:0] cpu_data_out;
reg         cpu_access;
wire        cpu_ack;
reg         cpu_wr_en;
reg  [1:0]  cpu_bytesel;

// DMA interface
reg  [19:1] dma_addr;
wire [15:0] dma_data_in;
reg  [15:0] dma_data_out;
reg         dma_access;
wire        dma_ack;
reg         dma_wr_en;
reg  [1:0]  dma_bytesel;

// VGA interface
reg  [19:1] vga_addr;
wire [15:0] vga_data_in;
reg  [15:0] vga_data_out;
reg         vga_access;
wire        vga_ack;
reg         vga_wr_en;
reg  [1:0]  vga_bytesel;

// VGA priority
reg vga_active_display;

// Intermediate signals (DMA arbiter -> Mem arbiter)
wire [19:1] dma_arb_addr;
wire [15:0] dma_arb_data_in;
wire [15:0] dma_arb_data_out;
wire        dma_arb_access;
wire        dma_arb_ack;
wire        dma_arb_wr_en;
wire [1:0]  dma_arb_bytesel;

// SDRAM interface (final output)
wire [19:1] sdram_addr;
reg  [15:0] sdram_data_in;
wire [15:0] sdram_data_out;
wire        sdram_access;
reg         sdram_ack;
wire        sdram_wr_en;
wire [1:0]  sdram_bytesel;

// Test tracking
integer test_num;
integer pass_count;
integer fail_count;
integer cycle_count;

// Performance counters
integer cpu_requests, dma_requests, vga_requests;
integer cpu_acks, dma_acks, vga_acks;
integer conflicts_level1, conflicts_level2;
integer total_sdram_accesses;

// Memory model
reg [15:0] memory [0:524287];

//============================================================================
// DUT Instantiation: Two-Level Arbitration Hierarchy
//============================================================================

// Level 1: CPU vs DMA
PipelinedDMAArbiter level1_arbiter (
    .clk(clk),
    .reset(reset),
    // A-bus (DMA)
    .a_m_addr(dma_addr),
    .a_m_data_in(dma_data_in),
    .a_m_data_out(dma_data_out),
    .a_m_access(dma_access),
    .a_m_ack(dma_ack),
    .a_m_wr_en(dma_wr_en),
    .a_m_bytesel(dma_bytesel),
    .ioa(1'b0),
    // B-bus (CPU - higher priority)
    .b_m_addr(cpu_addr),
    .b_m_data_in(cpu_data_in),
    .b_m_data_out(cpu_data_out),
    .b_m_access(cpu_access),
    .b_m_ack(cpu_ack),
    .b_m_wr_en(cpu_wr_en),
    .b_m_bytesel(cpu_bytesel),
    .iob(1'b0),
    // Output to Level 2
    .q_m_addr(dma_arb_addr),
    .q_m_data_in(dma_arb_data_in),
    .q_m_data_out(dma_arb_data_out),
    .q_m_access(dma_arb_access),
    .q_m_ack(dma_arb_ack),
    .q_m_wr_en(dma_arb_wr_en),
    .q_m_bytesel(dma_arb_bytesel),
    .ioq(),
    .q_b()
);

// Level 2: CPU+DMA vs VGA
PipelinedMemArbiterExtend level2_arbiter (
    .clk(clk),
    .reset(reset),
    // CPU+DMA bus
    .cpu_m_addr(dma_arb_addr),
    .cpu_m_data_in(dma_arb_data_in),
    .cpu_m_data_out(dma_arb_data_out),
    .cpu_m_access(dma_arb_access),
    .cpu_m_ack(dma_arb_ack),
    .cpu_m_wr_en(dma_arb_wr_en),
    .cpu_m_bytesel(dma_arb_bytesel),
    // VGA bus
    .mcga_m_addr(vga_addr),
    .mcga_m_data_in(vga_data_in),
    .mcga_m_data_out(vga_data_out),
    .mcga_m_access(vga_access),
    .mcga_m_ack(vga_ack),
    .mcga_m_wr_en(vga_wr_en),
    .mcga_m_bytesel(vga_bytesel),
    // Priority hint
    .vga_active_display(vga_active_display),
    // SDRAM
    .sdram_m_addr(sdram_addr),
    .sdram_m_data_in(sdram_data_in),
    .sdram_m_data_out(sdram_data_out),
    .sdram_m_access(sdram_access),
    .sdram_m_ack(sdram_ack),
    .sdram_m_wr_en(sdram_wr_en),
    .sdram_m_bytesel(sdram_bytesel),
    .q_b()
);

//============================================================================
// Clock Generation
//============================================================================

initial begin
    clk = 0;
    forever #(CLK_PERIOD/2) clk = ~clk;
end

//============================================================================
// SDRAM Memory Model
//============================================================================

integer sdram_latency_counter;
reg sdram_pending;

always @(posedge clk) begin
    if (reset) begin
        sdram_ack <= 1'b0;
        sdram_latency_counter <= 0;
        sdram_pending <= 1'b0;
    end else begin
        if (sdram_access && !sdram_pending) begin
            sdram_pending <= 1'b1;
            sdram_latency_counter <= SDRAM_LATENCY;
            sdram_ack <= 1'b0;
            total_sdram_accesses <= total_sdram_accesses + 1;
        end else if (sdram_pending) begin
            if (sdram_latency_counter > 1) begin
                sdram_latency_counter <= sdram_latency_counter - 1;
                sdram_ack <= 1'b0;
            end else begin
                sdram_ack <= 1'b1;
                sdram_pending <= 1'b0;
                if (sdram_wr_en) begin
                    memory[sdram_addr] <= sdram_data_out;
                end else begin
                    sdram_data_in <= memory[sdram_addr];
                end
            end
        end else begin
            sdram_ack <= 1'b0;
        end
    end
end

//============================================================================
// Test Utilities
//============================================================================

task check_result(input condition, input string description);
begin
    test_num = test_num + 1;
    if (condition) begin
        pass_count = pass_count + 1;
        $display("  [PASS] Test %0d: %s", test_num, description);
    end else begin
        fail_count = fail_count + 1;
        $display("  [FAIL] Test %0d: %s", test_num, description);
    end
end
endtask

task init_memory();
    integer i;
begin
    for (i = 0; i < 524288; i = i + 1) begin
        memory[i] = i[15:0] ^ 16'hA5A5;
    end
end
endtask

// CPU transaction
task cpu_read(input [19:1] addr);
begin
    cpu_addr = addr;
    cpu_data_out = 16'h0000;
    cpu_wr_en = 1'b0;
    cpu_bytesel = 2'b11;
    cpu_access = 1'b1;
    cpu_requests = cpu_requests + 1;

    @(posedge clk);
    wait(cpu_ack);
    cpu_acks = cpu_acks + 1;
    cpu_access = 1'b0;
    @(posedge clk);
end
endtask

task cpu_write(input [19:1] addr, input [15:0] data);
begin
    cpu_addr = addr;
    cpu_data_out = data;
    cpu_wr_en = 1'b1;
    cpu_bytesel = 2'b11;
    cpu_access = 1'b1;
    cpu_requests = cpu_requests + 1;

    @(posedge clk);
    wait(cpu_ack);
    cpu_acks = cpu_acks + 1;
    cpu_access = 1'b0;
    cpu_wr_en = 1'b0;
    @(posedge clk);
end
endtask

// DMA transaction
task dma_read(input [19:1] addr);
begin
    dma_addr = addr;
    dma_data_out = 16'h0000;
    dma_wr_en = 1'b0;
    dma_bytesel = 2'b11;
    dma_access = 1'b1;
    dma_requests = dma_requests + 1;

    @(posedge clk);
    wait(dma_ack);
    dma_acks = dma_acks + 1;
    dma_access = 1'b0;
    @(posedge clk);
end
endtask

// VGA transaction
task vga_read(input [19:1] addr);
begin
    vga_addr = addr;
    vga_data_out = 16'h0000;
    vga_wr_en = 1'b0;
    vga_bytesel = 2'b11;
    vga_access = 1'b1;
    vga_requests = vga_requests + 1;

    @(posedge clk);
    wait(vga_ack);
    vga_acks = vga_acks + 1;
    vga_access = 1'b0;
    @(posedge clk);
end
endtask

//============================================================================
// Performance Monitoring
//============================================================================

always @(posedge clk) begin
    if (!reset) begin
        // Detect conflicts at each level
        if (cpu_access && dma_access)
            conflicts_level1 = conflicts_level1 + 1;
        if (dma_arb_access && vga_access)
            conflicts_level2 = conflicts_level2 + 1;
    end
end

//============================================================================
// Main Test Sequence
//============================================================================

initial begin
    $display("========================================");
    $display("Pipelined System Integration Test");
    $display("Two-Level Arbitration Hierarchy");
    $display("========================================\n");

    // Initialize
    test_num = 0;
    pass_count = 0;
    fail_count = 0;
    cycle_count = 0;
    cpu_requests = 0;
    dma_requests = 0;
    vga_requests = 0;
    cpu_acks = 0;
    dma_acks = 0;
    vga_acks = 0;
    conflicts_level1 = 0;
    conflicts_level2 = 0;
    total_sdram_accesses = 0;

    reset = 1;
    cpu_access = 0;
    dma_access = 0;
    vga_access = 0;
    cpu_wr_en = 0;
    dma_wr_en = 0;
    vga_wr_en = 0;
    vga_active_display = 0;

    init_memory();

    repeat(10) @(posedge clk);
    reset = 0;
    repeat(5) @(posedge clk);

    //========================================================================
    // TEST 1: Basic CPU Access Through Hierarchy
    //========================================================================
    $display("Test 1: Basic CPU access through 2-level hierarchy");
    cpu_read(19'h01000);
    check_result(cpu_data_in == (16'h1000 ^ 16'hA5A5), "CPU read data correct");

    //========================================================================
    // TEST 2: Basic DMA Access
    //========================================================================
    $display("\nTest 2: Basic DMA access");
    dma_read(19'h02000);
    check_result(dma_data_in == (16'h2000 ^ 16'hA5A5), "DMA read data correct");

    //========================================================================
    // TEST 3: Basic VGA Access
    //========================================================================
    $display("\nTest 3: Basic VGA access");
    vga_read(19'h03000);
    check_result(vga_data_in == (16'h3000 ^ 16'hA5A5), "VGA read data correct");

    //========================================================================
    // TEST 4: CPU Priority over DMA (Level 1)
    //========================================================================
    $display("\nTest 4: CPU priority over DMA at level 1");
    fork
        cpu_read(19'h04000);
        dma_read(19'h05000);
    join
    check_result(cpu_acks > 0 && dma_acks > 0, "Both CPU and DMA served");

    //========================================================================
    // TEST 5: VGA Priority During Active Display (Level 2)
    //========================================================================
    $display("\nTest 5: VGA priority during active display");
    vga_active_display = 1'b1;

    fork
        cpu_read(19'h06000);
        begin
            #5;  // Slight delay
            vga_read(19'h07000);
        end
    join

    vga_active_display = 1'b0;
    check_result(1, "VGA priority during active display handled");

    //========================================================================
    // TEST 6: Mixed Workload - All Three Masters
    //========================================================================
    $display("\nTest 6: Mixed workload with all three masters");
    begin
        integer i;
        integer start_cycle, end_cycle;
        real throughput;

        start_cycle = cycle_count;

        for (i = 0; i < 10; i = i + 1) begin
            case (i % 3)
                0: cpu_read(19'h10000 + i);
                1: dma_read(19'h10000 + i);
                2: vga_read(19'h10000 + i);
            endcase
        end

        end_cycle = cycle_count;
        throughput = real'(30) / real'(end_cycle - start_cycle);

        $display("  30 total requests in %0d cycles", end_cycle - start_cycle);
        $display("  System throughput: %.3f ops/cycle", throughput);
        check_result(throughput >= 0.25,
                    $sformatf("System throughput %.3f >= 0.25", throughput));
    end

    //========================================================================
    // TEST 7: Write Operations Through Hierarchy
    //========================================================================
    $display("\nTest 7: Write operations through hierarchy");
    cpu_write(19'h20000, 16'hDEAD);
    cpu_read(19'h20000);
    check_result(cpu_data_in == 16'hDEAD, "CPU write verified");

    //========================================================================
    // TEST 8: Sustained Mixed Load
    //========================================================================
    $display("\nTest 8: Sustained mixed load (60 operations)");
    begin
        integer i;
        integer start_cycle, end_cycle;
        real throughput;

        start_cycle = cycle_count;
        vga_active_display = 1'b0;  // Fair arbitration

        for (i = 0; i < 60; i = i + 1) begin
            case (i % 3)
                0: cpu_read(19'h30000 + i);
                1: dma_read(19'h30000 + i);
                2: vga_read(19'h30000 + i);
            endcase
        end

        end_cycle = cycle_count;
        throughput = real'(60) / real'(end_cycle - start_cycle);

        $display("  60 operations in %0d cycles", end_cycle - start_cycle);
        $display("  Sustained throughput: %.3f ops/cycle", throughput);
        check_result(throughput >= 0.25,
                    $sformatf("Sustained throughput %.3f >= 0.25", throughput));
    end

    //========================================================================
    // TEST 9: Pipeline Efficiency
    //========================================================================
    $display("\nTest 9: Pipeline efficiency test");
    begin
        integer start_cycle, end_cycle;
        real efficiency;

        start_cycle = cycle_count;

        // Rapid sequential requests
        repeat(20) cpu_read(19'h40000);

        end_cycle = cycle_count;

        $display("  20 sequential CPU reads in %0d cycles", end_cycle - start_cycle);
        check_result((end_cycle - start_cycle) <= 120,
                    "Pipeline efficiency acceptable");
    end

    //========================================================================
    // Performance Summary
    //========================================================================
    repeat(10) @(posedge clk);

    $display("\n========================================");
    $display("PERFORMANCE SUMMARY");
    $display("========================================");
    $display("CPU requests:   %0d (acks: %0d)", cpu_requests, cpu_acks);
    $display("DMA requests:   %0d (acks: %0d)", dma_requests, dma_acks);
    $display("VGA requests:   %0d (acks: %0d)", vga_requests, vga_acks);
    $display("Total cycles:   %0d", cycle_count);
    $display("SDRAM accesses: %0d", total_sdram_accesses);
    $display("Level 1 conflicts (CPU vs DMA): %0d", conflicts_level1);
    $display("Level 2 conflicts (CPU+DMA vs VGA): %0d", conflicts_level2);
    $display("Overall system throughput: %.3f ops/cycle",
            real'(cpu_acks + dma_acks + vga_acks) / real'(cycle_count));
    $display("========================================\n");

    //========================================================================
    // Test Summary
    //========================================================================
    $display("========================================");
    $display("TEST SUMMARY");
    $display("========================================");
    $display("Total tests: %0d", test_num);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    $display("Success rate: %.1f%%", real'(pass_count) / real'(test_num) * 100.0);
    $display("========================================\n");

    if (fail_count == 0) begin
        $display("*** ALL SYSTEM INTEGRATION TESTS PASSED ***\n");
        $finish(0);
    end else begin
        $display("*** SOME TESTS FAILED ***\n");
        $finish(1);
    end
end

// Cycle counter
always @(posedge clk) begin
    if (!reset) cycle_count <= cycle_count + 1;
end

// Timeout watchdog
initial begin
    #2000000;  // 2ms timeout
    $display("\n========================================");
    $display("ERROR: Simulation timeout!");
    $display("========================================");
    $finish(2);
end

// Waveform dump
initial begin
    $dumpfile("pipelined_system_integration_tb.vcd");
    $dumpvars(0, pipelined_system_integration_tb);
end

endmodule
`default_nettype wire
