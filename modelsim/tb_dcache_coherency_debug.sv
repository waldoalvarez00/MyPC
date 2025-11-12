// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// DEBUG VERSION - Cache Coherency Testbench
// Focused test with extensive debug traces to identify sequential operation issue

`timescale 1ns / 1ps

module tb_dcache_coherency_debug;

    // Clock and reset
    logic clk;
    logic reset;

    // Test tracking
    integer cycle_count;
    string test_phase;

    // CPU signals
    logic [19:1] cpu_addr;
    logic [15:0] cpu_data_in;
    logic [15:0] cpu_data_out;
    logic cpu_access;
    logic cpu_ack;
    logic cpu_wr_en;
    logic [1:0] cpu_bytesel;

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
    logic [15:0] memory [0:4095];
    integer i;

    //==========================================================================
    // Module Instantiations
    //==========================================================================

    // DCacheFrontendArbiter - Multiplexes CPU/FPU to D-cache
    // (Simplified - removed DMA for focused debugging)
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

        // DMA port (unused)
        .dma_addr(19'h00000),
        .dma_data_in(),
        .dma_data_out(16'h0000),
        .dma_access(1'b0),
        .dma_ack(),
        .dma_wr_en(1'b0),
        .dma_bytesel(2'b11),

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
    DCache2Way #(.sets(64)) dcache (
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
        forever #5 clk = ~clk;
    end

    //==========================================================================
    // Cycle Counter
    //==========================================================================

    always_ff @(posedge clk) begin
        if (reset)
            cycle_count <= 0;
        else
            cycle_count <= cycle_count + 1;
    end

    //==========================================================================
    // Simulated SDRAM Backend
    //==========================================================================

    always_ff @(posedge clk) begin
        if (reset) begin
            cache_m_ack <= 1'b0;
            cache_m_data_in <= 16'b0;
        end else begin
            cache_m_ack <= cache_m_access;

            if (cache_m_access) begin
                if (cache_m_wr_en) begin
                    if (cache_m_bytesel[0])
                        memory[cache_m_addr[12:1]][7:0] <= cache_m_data_out[7:0];
                    if (cache_m_bytesel[1])
                        memory[cache_m_addr[12:1]][15:8] <= cache_m_data_out[15:8];
                    $display("[%04d] SDRAM: Write addr=%05h data=%04h bytesel=%b",
                             cycle_count, cache_m_addr, cache_m_data_out, cache_m_bytesel);
                end else begin
                    cache_m_data_in <= memory[cache_m_addr[12:1]];
                    $display("[%04d] SDRAM: Read  addr=%05h data=%04h",
                             cycle_count, cache_m_addr, memory[cache_m_addr[12:1]]);
                end
            end
        end
    end

    //==========================================================================
    // Debug Monitors
    //==========================================================================

    // Monitor arbiter state
    always_ff @(posedge clk) begin
        if (!reset) begin
            // Monitor arbiter inputs
            if (cpu_access || fpu_access) begin
                $display("[%04d] ARBITER IN:  cpu_acc=%b cpu_addr=%05h fpu_acc=%b fpu_addr=%05h",
                         cycle_count, cpu_access, cpu_addr, fpu_access, fpu_addr);
            end

            // Monitor arbiter outputs
            if (cache_c_access) begin
                $display("[%04d] ARBITER OUT: cache_acc=%b cache_addr=%05h cache_wr=%b cache_data=%04h",
                         cycle_count, cache_c_access, cache_c_addr, cache_c_wr_en, cache_c_data_out);
            end

            // Monitor ACKs
            if (cpu_ack) begin
                $display("[%04d] ARBITER ACK: CPU acknowledged (data=%04h)",
                         cycle_count, cpu_data_in);
            end
            if (fpu_ack) begin
                $display("[%04d] ARBITER ACK: FPU acknowledged (data=%04h)",
                         cycle_count, fpu_data_in);
            end
        end
    end

    // Monitor cache frontend
    always_ff @(posedge clk) begin
        if (!reset && cache_c_access) begin
            $display("[%04d] CACHE FE:    access=%b wr=%b addr=%05h data_out=%04h",
                     cycle_count, cache_c_access, cache_c_wr_en, cache_c_addr, cache_c_data_out);
        end
        if (!reset && cache_c_ack) begin
            $display("[%04d] CACHE FE:    ACK (data_in=%04h)",
                     cycle_count, cache_c_data_in);
        end
    end

    // Monitor cache backend
    always_ff @(posedge clk) begin
        if (!reset && cache_m_access) begin
            $display("[%04d] CACHE BE:    access=%b wr=%b addr=%05h",
                     cycle_count, cache_m_access, cache_m_wr_en, cache_m_addr);
        end
    end

    //==========================================================================
    // Main Test Sequence
    //==========================================================================

    initial begin
        $display("=================================================================");
        $display("D-Cache Sequential Operation Debug Test");
        $display("=================================================================");
        $display("Focused test: CPU Write → FPU Read");
        $display("");

        // Initialize
        reset = 1;
        cpu_access = 0;
        fpu_access = 0;
        cpu_wr_en = 0;
        fpu_wr_en = 0;
        cpu_bytesel = 2'b11;
        fpu_bytesel = 2'b11;
        test_phase = "RESET";

        // Initialize memory
        for (i = 0; i < 4096; i = i + 1) begin
            memory[i] = 16'h0000;
        end

        // Release reset
        repeat(10) @(posedge clk);
        $display("[%04d] ========== Releasing Reset ==========", cycle_count);
        reset = 0;
        repeat(20) @(posedge clk);

        //======================================================================
        // PHASE 1: CPU Write
        //======================================================================
        test_phase = "CPU_WRITE";
        $display("");
        $display("[%04d] ========== PHASE 1: CPU Write ==========", cycle_count);
        $display("[%04d] CPU will write 0x1234 to address 0x00200", cycle_count);
        $display("");

        @(posedge clk);
        cpu_addr = 19'h00200;
        cpu_data_out = 16'h1234;
        cpu_wr_en = 1'b1;
        cpu_bytesel = 2'b11;
        cpu_access = 1'b1;

        $display("[%04d] CPU: Write initiated addr=%05h data=%04h", cycle_count, cpu_addr, cpu_data_out);

        // Wait for ACK
        fork
            begin
                wait(cpu_ack);
                $display("[%04d] CPU: Write acknowledged!", cycle_count);
            end
            begin
                repeat(100) @(posedge clk);
                if (!cpu_ack) begin
                    $display("[%04d] ERROR: CPU write timeout!", cycle_count);
                    $finish(1);
                end
            end
        join_any
        disable fork;

        @(posedge clk);
        cpu_access = 1'b0;
        cpu_wr_en = 1'b0;

        $display("[%04d] CPU: Write complete, waiting for cache to settle...", cycle_count);
        repeat(100) @(posedge clk);

        //======================================================================
        // PHASE 2: FPU Read (Same Address)
        //======================================================================
        test_phase = "FPU_READ";
        $display("");
        $display("[%04d] ========== PHASE 2: FPU Read (Same Address) ==========", cycle_count);
        $display("[%04d] FPU will read from address 0x00200 (should see 0x1234)", cycle_count);
        $display("");

        @(posedge clk);
        fpu_addr = 19'h00200;
        fpu_wr_en = 1'b0;
        fpu_bytesel = 2'b11;
        fpu_access = 1'b1;

        $display("[%04d] FPU: Read initiated addr=%05h", cycle_count, fpu_addr);

        // Wait for ACK with detailed monitoring
        fork
            begin
                wait(fpu_ack);
                $display("[%04d] FPU: Read acknowledged! data=%04h", cycle_count, fpu_data_in);
            end
            begin
                integer wait_cycles;
                wait_cycles = 0;
                while (!fpu_ack && wait_cycles < 200) begin
                    @(posedge clk);
                    wait_cycles = wait_cycles + 1;
                    if (wait_cycles % 10 == 0) begin
                        $display("[%04d] FPU: Still waiting (%0d cycles)... fpu_access=%b cache_c_access=%b cache_c_ack=%b",
                                 cycle_count, wait_cycles, fpu_access, cache_c_access, cache_c_ack);
                    end
                end
                if (!fpu_ack) begin
                    $display("[%04d] ERROR: FPU read timeout after %0d cycles!", cycle_count, wait_cycles);
                    $display("");
                    $display("Final state dump:");
                    $display("  fpu_access     = %b", fpu_access);
                    $display("  fpu_ack        = %b", fpu_ack);
                    $display("  cache_c_access = %b", cache_c_access);
                    $display("  cache_c_ack    = %b", cache_c_ack);
                    $display("  cache_m_access = %b", cache_m_access);
                    $display("  cache_m_ack    = %b", cache_m_ack);
                    $finish(1);
                end
            end
        join_any
        disable fork;

        @(posedge clk);
        fpu_access = 1'b0;

        //======================================================================
        // Verify Result
        //======================================================================
        $display("");
        $display("[%04d] ========== Verification ==========", cycle_count);
        if (fpu_data_in === 16'h1234) begin
            $display("[%04d] ✓✓✓ SUCCESS: FPU read correct data (0x%04h)", cycle_count, fpu_data_in);
            $display("");
            $display("=================================================================");
            $display("Cache Sequential Operation Test PASSED");
            $display("=================================================================");
            $finish(0);
        end else begin
            $display("[%04d] ✗✗✗ FAILURE: FPU read wrong data (expected=0x1234, actual=0x%04h)",
                     cycle_count, fpu_data_in);
            $finish(1);
        end
    end

    // Global timeout
    initial begin
        #50000;  // 50μs timeout
        $display("ERROR: Global test timeout!");
        $finish(1);
    end

endmodule
