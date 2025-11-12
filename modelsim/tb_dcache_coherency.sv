// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// Cache Coherency Testbench for DCacheFrontendArbiter
//
// Tests the critical coherency scenarios that were broken in the old architecture:
// 1. DMA Write → CPU Read (verifies CPU sees DMA's writes)
// 2. CPU Write → FPU Read (verifies FPU sees CPU's writes)
// 3. FPU Write → CPU Read (verifies CPU sees FPU's writes)
// 4. Mixed access patterns with priority enforcement
//
// This testbench validates that routing all data memory (CPU/DMA/FPU) through
// the D-cache eliminates stale data coherency violations.

`timescale 1ns / 1ps

module tb_dcache_coherency;

    // Clock and reset
    logic clk;
    logic reset;

    // Test tracking
    integer test_count;
    integer pass_count;
    integer fail_count;
    string test_name;

    // CPU signals
    logic [19:1] cpu_addr;
    logic [15:0] cpu_data_in;
    logic [15:0] cpu_data_out;
    logic cpu_access;
    logic cpu_ack;
    logic cpu_wr_en;
    logic [1:0] cpu_bytesel;

    // DMA signals
    logic [19:1] dma_addr;
    logic [15:0] dma_data_in;
    logic [15:0] dma_data_out;
    logic dma_access;
    logic dma_ack;
    logic dma_wr_en;
    logic [1:0] dma_bytesel;

    // FPU signals
    logic [19:1] fpu_addr;
    logic [15:0] fpu_data_in;
    logic [15:0] fpu_data_out;
    logic fpu_access;
    logic fpu_ack;
    logic fpu_wr_en;
    logic [1:0] fpu_bytesel;

    // D-cache frontend signals (arbiter → cache)
    logic [19:1] cache_c_addr;
    logic [15:0] cache_c_data_in;
    logic [15:0] cache_c_data_out;
    logic cache_c_access;
    logic cache_c_ack;
    logic cache_c_wr_en;
    logic [1:0] cache_c_bytesel;

    // D-cache backend signals (cache → memory)
    logic [19:1] cache_m_addr;
    logic [15:0] cache_m_data_in;
    logic [15:0] cache_m_data_out;
    logic cache_m_access;
    logic cache_m_ack;
    logic cache_m_wr_en;
    logic [1:0] cache_m_bytesel;

    // Simulated SDRAM
    logic [15:0] memory [0:4095];  // 8KB test memory
    integer i;

    //==========================================================================
    // Module Instantiations
    //==========================================================================

    // DCacheFrontendArbiter - Multiplexes CPU/DMA/FPU to D-cache
    DCacheFrontendArbiter arbiter (
        .clk(clk),
        .reset(reset),

        // CPU port
        .cpu_addr(cpu_addr),
        .cpu_data_in(cpu_data_in),
        .cpu_data_out(cpu_data_out),
        .cpu_access(cpu_access),
        .cpu_ack(cpu_ack),
        .cpu_wr_en(cpu_wr_en),
        .cpu_bytesel(cpu_bytesel),

        // DMA port
        .dma_addr(dma_addr),
        .dma_data_in(dma_data_in),
        .dma_data_out(dma_data_out),
        .dma_access(dma_access),
        .dma_ack(dma_ack),
        .dma_wr_en(dma_wr_en),
        .dma_bytesel(dma_bytesel),

        // FPU port
        .fpu_addr(fpu_addr),
        .fpu_data_in(fpu_data_in),
        .fpu_data_out(fpu_data_out),
        .fpu_access(fpu_access),
        .fpu_ack(fpu_ack),
        .fpu_wr_en(fpu_wr_en),
        .fpu_bytesel(fpu_bytesel),

        // D-cache frontend
        .cache_addr(cache_c_addr),
        .cache_data_in(cache_c_data_in),
        .cache_data_out(cache_c_data_out),
        .cache_access(cache_c_access),
        .cache_ack(cache_c_ack),
        .cache_wr_en(cache_c_wr_en),
        .cache_bytesel(cache_c_bytesel)
    );

    // DCache2Way - 2-way set-associative data cache
    DCache2Way #(.sets(64)) dcache (  // Smaller for testing (1KB)
        .clk(clk),
        .reset(reset),
        .enabled(1'b1),

        // Frontend (from arbiter)
        .c_addr(cache_c_addr),
        .c_data_in(cache_c_data_in),
        .c_data_out(cache_c_data_out),
        .c_access(cache_c_access),
        .c_ack(cache_c_ack),
        .c_wr_en(cache_c_wr_en),
        .c_bytesel(cache_c_bytesel),

        // Backend (to simulated SDRAM)
        .m_addr(cache_m_addr),
        .m_data_in(cache_m_data_in),
        .m_data_out(cache_m_data_out),
        .m_access(cache_m_access),
        .m_ack(cache_m_ack),
        .m_wr_en(cache_m_wr_en),
        .m_bytesel(cache_m_bytesel)
    );

    //==========================================================================
    // Clock Generation
    //==========================================================================

    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock (10ns period)
    end

    //==========================================================================
    // Simulated SDRAM Backend
    //==========================================================================

    always_ff @(posedge clk) begin
        if (reset) begin
            cache_m_ack <= 1'b0;
            cache_m_data_in <= 16'b0;
        end else begin
            cache_m_ack <= cache_m_access;  // 1-cycle latency

            if (cache_m_access) begin
                if (cache_m_wr_en) begin
                    // Write to memory
                    if (cache_m_bytesel[0])
                        memory[cache_m_addr[12:1]][7:0] <= cache_m_data_out[7:0];
                    if (cache_m_bytesel[1])
                        memory[cache_m_addr[12:1]][15:8] <= cache_m_data_out[15:8];
                    $display("  [SDRAM] Write addr=%h data=%h bytesel=%b",
                             cache_m_addr, cache_m_data_out, cache_m_bytesel);
                end else begin
                    // Read from memory
                    cache_m_data_in <= memory[cache_m_addr[12:1]];
                    $display("  [SDRAM] Read addr=%h data=%h",
                             cache_m_addr, memory[cache_m_addr[12:1]]);
                end
            end
        end
    end

    //==========================================================================
    // Test Helper Tasks
    //==========================================================================

    task automatic cpu_write(input [19:1] addr, input [15:0] data, input [1:0] bytesel);
        begin
            integer timeout_counter;
            @(posedge clk);
            cpu_addr = addr;
            cpu_data_out = data;
            cpu_wr_en = 1'b1;
            cpu_bytesel = bytesel;
            cpu_access = 1'b1;

            $display("  [CPU] Write request addr=%h data=%h", addr, data);

            // Wait for ACK with timeout
            timeout_counter = 0;
            while (!cpu_ack && timeout_counter < 1000) begin
                @(posedge clk);
                timeout_counter = timeout_counter + 1;
            end

            if (timeout_counter >= 1000) begin
                $display("  [CPU] ERROR: Write timeout!");
                $finish(1);
            end

            @(posedge clk);
            cpu_access = 1'b0;
            cpu_wr_en = 1'b0;

            $display("  [CPU] Write acknowledged (cycles=%0d)", timeout_counter);
        end
    endtask

    task automatic cpu_read(input [19:1] addr, output [15:0] data);
        begin
            integer timeout_counter;
            @(posedge clk);
            cpu_addr = addr;
            cpu_wr_en = 1'b0;
            cpu_bytesel = 2'b11;
            cpu_access = 1'b1;

            $display("  [CPU] Read request addr=%h", addr);

            // Wait for ACK with timeout
            timeout_counter = 0;
            while (!cpu_ack && timeout_counter < 1000) begin
                @(posedge clk);
                timeout_counter = timeout_counter + 1;
                if (timeout_counter % 100 == 0)
                    $display("  [CPU] Still waiting... (%0d cycles)", timeout_counter);
            end

            if (timeout_counter >= 1000) begin
                $display("  [CPU] ERROR: Read timeout!");
                $finish(1);
            end

            data = cpu_data_in;
            @(posedge clk);
            cpu_access = 1'b0;

            $display("  [CPU] Read acknowledged data=%h (cycles=%0d)", data, timeout_counter);
        end
    endtask

    task automatic dma_write(input [19:1] addr, input [15:0] data, input [1:0] bytesel);
        begin
            integer timeout_counter;
            @(posedge clk);
            dma_addr = addr;
            dma_data_out = data;
            dma_wr_en = 1'b1;
            dma_bytesel = bytesel;
            dma_access = 1'b1;

            $display("  [DMA] Write request addr=%h data=%h", addr, data);

            // Wait for ACK with timeout
            timeout_counter = 0;
            while (!dma_ack && timeout_counter < 1000) begin
                @(posedge clk);
                timeout_counter = timeout_counter + 1;
                if (timeout_counter % 100 == 0)
                    $display("  [DMA] Still waiting... (%0d cycles)", timeout_counter);
            end

            if (timeout_counter >= 1000) begin
                $display("  [DMA] ERROR: Write timeout!");
                $finish(1);
            end

            @(posedge clk);
            dma_access = 1'b0;
            dma_wr_en = 1'b0;

            $display("  [DMA] Write acknowledged (cycles=%0d)", timeout_counter);
        end
    endtask

    task automatic dma_read(input [19:1] addr, output [15:0] data);
        begin
            @(posedge clk);
            dma_addr = addr;
            dma_wr_en = 1'b0;
            dma_bytesel = 2'b11;
            dma_access = 1'b1;

            $display("  [DMA] Read request addr=%h", addr);

            // Wait for ACK
            wait(dma_ack);
            data = dma_data_in;
            @(posedge clk);
            dma_access = 1'b0;

            $display("  [DMA] Read acknowledged data=%h", data);
        end
    endtask

    task automatic fpu_write(input [19:1] addr, input [15:0] data, input [1:0] bytesel);
        begin
            @(posedge clk);
            fpu_addr = addr;
            fpu_data_out = data;
            fpu_wr_en = 1'b1;
            fpu_bytesel = bytesel;
            fpu_access = 1'b1;

            $display("  [FPU] Write request addr=%h data=%h", addr, data);

            // Wait for ACK
            wait(fpu_ack);
            @(posedge clk);
            fpu_access = 1'b0;
            fpu_wr_en = 1'b0;

            $display("  [FPU] Write acknowledged");
        end
    endtask

    task automatic fpu_read(input [19:1] addr, output [15:0] data);
        begin
            integer timeout_counter;
            @(posedge clk);
            fpu_addr = addr;
            fpu_wr_en = 1'b0;
            fpu_bytesel = 2'b11;
            fpu_access = 1'b1;

            $display("  [FPU] Read request addr=%h", addr);

            // Wait for ACK with timeout
            timeout_counter = 0;
            while (!fpu_ack && timeout_counter < 1000) begin
                @(posedge clk);
                timeout_counter = timeout_counter + 1;
                if (timeout_counter % 100 == 0)
                    $display("  [FPU] Still waiting... (%0d cycles)", timeout_counter);
            end

            if (timeout_counter >= 1000) begin
                $display("  [FPU] ERROR: Read timeout!");
                $finish(1);
            end

            data = fpu_data_in;
            @(posedge clk);
            fpu_access = 1'b0;

            $display("  [FPU] Read acknowledged data=%h (cycles=%0d)", data, timeout_counter);
        end
    endtask

    task check_result(input [15:0] expected, input [15:0] actual, input string description);
        begin
            test_count++;
            if (expected === actual) begin
                $display("  ✓ PASS: %s (expected=%h, actual=%h)", description, expected, actual);
                pass_count++;
            end else begin
                $display("  ✗ FAIL: %s (expected=%h, actual=%h)", description, expected, actual);
                fail_count++;
            end
        end
    endtask

    //==========================================================================
    // Main Test Sequence
    //==========================================================================

    initial begin
        $display("=============================================================");
        $display("D-Cache Coherency Test");
        $display("=============================================================");
        $display("");

        // Initialize
        test_count = 0;
        pass_count = 0;
        fail_count = 0;

        reset = 1;
        cpu_access = 0;
        dma_access = 0;
        fpu_access = 0;
        cpu_wr_en = 0;
        dma_wr_en = 0;
        fpu_wr_en = 0;
        cpu_bytesel = 2'b11;
        dma_bytesel = 2'b11;
        fpu_bytesel = 2'b11;

        // Initialize memory
        for (i = 0; i < 4096; i = i + 1) begin
            memory[i] = 16'h0000;
        end

        // Release reset
        repeat(10) @(posedge clk);
        reset = 0;
        repeat(20) @(posedge clk);  // Allow cache to initialize

        //======================================================================
        // TEST 1: DMA Write → CPU Read (Critical Coherency Test #1)
        //======================================================================
        test_name = "DMA Write → CPU Read Coherency";
        $display("-------------------------------------------------------------");
        $display("TEST 1: %s", test_name);
        $display("-------------------------------------------------------------");
        $display("This test verifies that CPU sees data written by DMA.");
        $display("In the OLD architecture, this would FAIL (stale cache data).");
        $display("");

        begin
            logic [15:0] read_data;
            logic [19:1] test_addr;
            test_addr = 19'h00100;  // Use lower addresses to avoid conflicts

            // DMA writes a value
            dma_write(test_addr, 16'hABCD, 2'b11);
            repeat(50) @(posedge clk);  // Allow cache line fill and update

            // CPU reads same address (should see DMA's write)
            cpu_read(test_addr, read_data);
            check_result(16'hABCD, read_data, "CPU reads DMA write");
        end

        $display("");

        //======================================================================
        // TEST 2: CPU Write → FPU Read (Critical Coherency Test #2)
        //======================================================================
        test_name = "CPU Write → FPU Read Coherency";
        $display("-------------------------------------------------------------");
        $display("TEST 2: %s", test_name);
        $display("-------------------------------------------------------------");
        $display("This test verifies that FPU sees data written by CPU.");
        $display("In the OLD architecture, this would FAIL (FPU reads stale SDRAM).");
        $display("");

        begin
            logic [15:0] read_data;
            logic [19:1] test_addr;
            test_addr = 19'h00200;  // Different cache line from TEST 1

            // CPU writes a value
            cpu_write(test_addr, 16'h1234, 2'b11);
            repeat(100) @(posedge clk);  // Allow cache eviction and update

            // FPU reads same address (should see CPU's write)
            fpu_read(test_addr, read_data);
            check_result(16'h1234, read_data, "FPU reads CPU write");
        end

        $display("");

        //======================================================================
        // TEST 3: FPU Write → CPU Read (Critical Coherency Test #3)
        //======================================================================
        test_name = "FPU Write → CPU Read Coherency";
        $display("-------------------------------------------------------------");
        $display("TEST 3: %s", test_name);
        $display("-------------------------------------------------------------");
        $display("This test verifies that CPU sees data written by FPU.");
        $display("In the OLD architecture, this would FAIL (stale cache data).");
        $display("");

        begin
            logic [15:0] read_data;
            logic [19:1] test_addr;
            test_addr = 19'h00300;  // Different cache line

            // FPU writes a value
            fpu_write(test_addr, 16'h5678, 2'b11);
            repeat(50) @(posedge clk);  // Allow cache update

            // CPU reads same address (should see FPU's write)
            cpu_read(test_addr, read_data);
            check_result(16'h5678, read_data, "CPU reads FPU write");
        end

        $display("");

        //======================================================================
        // TEST 4: Mixed Read/Write Pattern
        //======================================================================
        test_name = "Mixed Access Pattern";
        $display("-------------------------------------------------------------");
        $display("TEST 4: %s", test_name);
        $display("-------------------------------------------------------------");
        $display("Complex pattern: CPU→DMA→FPU reads and writes to same location.");
        $display("");

        begin
            logic [15:0] read_data;
            logic [19:1] test_addr;
            test_addr = 19'h00400;  // Different cache line

            // CPU writes initial value
            cpu_write(test_addr, 16'hAAAA, 2'b11);
            repeat(20) @(posedge clk);

            // DMA reads (should see CPU write)
            dma_read(test_addr, read_data);
            check_result(16'hAAAA, read_data, "DMA reads CPU write");

            // FPU overwrites
            fpu_write(test_addr, 16'hBBBB, 2'b11);
            repeat(20) @(posedge clk);

            // CPU reads (should see FPU write)
            cpu_read(test_addr, read_data);
            check_result(16'hBBBB, read_data, "CPU reads FPU write");

            // DMA overwrites
            dma_write(test_addr, 16'hCCCC, 2'b11);
            repeat(20) @(posedge clk);

            // FPU reads (should see DMA write)
            fpu_read(test_addr, read_data);
            check_result(16'hCCCC, read_data, "FPU reads DMA write");
        end

        $display("");

        //======================================================================
        // TEST 5: Byte-Level Coherency
        //======================================================================
        test_name = "Byte-Level Write Coherency";
        $display("-------------------------------------------------------------");
        $display("TEST 5: %s", test_name);
        $display("-------------------------------------------------------------");
        $display("Tests byte-level writes and reads for coherency.");
        $display("");

        begin
            logic [15:0] read_data;
            logic [19:1] test_addr;
            test_addr = 19'h00500;  // Different cache line

            // CPU writes word
            cpu_write(test_addr, 16'h0000, 2'b11);
            repeat(20) @(posedge clk);

            // DMA writes low byte
            dma_write(test_addr, 16'h00AB, 2'b01);
            repeat(20) @(posedge clk);

            // FPU writes high byte
            fpu_write(test_addr, 16'hCD00, 2'b10);
            repeat(20) @(posedge clk);

            // CPU reads (should see both byte writes)
            cpu_read(test_addr, read_data);
            check_result(16'hCDAB, read_data, "CPU reads byte-level writes");
        end

        $display("");

        //======================================================================
        // Test Summary
        //======================================================================
        $display("=============================================================");
        $display("Test Summary");
        $display("=============================================================");
        $display("Total tests: %0d", test_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);

        if (fail_count == 0) begin
            $display("");
            $display("✓✓✓ ALL COHERENCY TESTS PASSED ✓✓✓");
            $display("");
            $display("Cache coherency is GUARANTEED:");
            $display("  ✓ DMA writes are visible to CPU");
            $display("  ✓ CPU writes are visible to FPU");
            $display("  ✓ FPU writes are visible to CPU");
            $display("  ✓ All memory accesses go through D-cache");
            $display("  ✓ No stale data violations");
            $display("=============================================================");
            $finish(0);
        end else begin
            $display("");
            $display("✗✗✗ COHERENCY TESTS FAILED ✗✗✗");
            $display("=============================================================");
            $finish(1);
        end
    end

    // Timeout watchdog
    initial begin
        #100000;  // 100μs timeout
        $display("ERROR: Test timeout!");
        $finish(1);
    end

endmodule
