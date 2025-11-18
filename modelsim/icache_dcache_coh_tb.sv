// Coherence testbench for ICache2Way + DCache2Way sideband
// - Verifies residency-based CODE_REGION behavior:
//   * I-cache line resident
//   * D-cache store to same address triggers write-through
//   * I-cache invalidates and refetches updated code

`timescale 1ns/1ps

module icache_dcache_coh_tb;

    // Clock/reset
    logic clk = 0;
    logic reset = 0;

    // Test tracking
    integer test_count;
    integer pass_count;
    integer fail_count;

    // I-cache frontend
    logic [19:1] ic_c_addr;
    logic [15:0] ic_c_data_in;
    logic        ic_c_access;
    logic        ic_c_ack;

    // I-cache backend
    logic [19:1] ic_m_addr;
    logic [15:0] ic_m_data_in;
    logic        ic_m_access;
    logic        ic_m_ack;

    // D-cache frontend
    logic [19:1] dc_c_addr;
    logic [15:0] dc_c_data_in;
    logic [15:0] dc_c_data_out;
    logic        dc_c_access;
    logic        dc_c_ack;
    logic        dc_c_wr_en;
    logic [1:0]  dc_c_bytesel;

    // D-cache backend
    logic [19:1] dc_m_addr;
    logic [15:0] dc_m_data_in;
    logic [15:0] dc_m_data_out;
    logic        dc_m_access;
    logic        dc_m_ack;
    logic        dc_m_wr_en;
    logic [1:0]  dc_m_bytesel;

    // Coherence sideband between D-cache and I-cache
    logic        coh_wr_valid;
    logic [19:1] coh_wr_addr;
    logic [15:0] coh_wr_data;
    logic [1:0]  coh_wr_bytesel;
    logic        coh_probe_valid;
    logic [19:1] coh_probe_addr;
    logic        coh_probe_present;

    // I-cache invalidation from SDRAM arbiter (unused here)
    logic        ic_inval_valid;
    logic [19:1] ic_inval_addr;

    // Shared backing memory (Harvard I/D but coherent storage)
    logic [15:0] memory [0:4095];

    // Clock generation
    always #5 clk = ~clk;

    // DUTs

    ICache2Way #(.sets(64)) icache (
        .clk      (clk),
        .reset    (reset),
        .enabled  (1'b1),

        // Frontend
        .c_addr   (ic_c_addr),
        .c_data_in(ic_c_data_in),
        .c_access (ic_c_access),
        .c_ack    (ic_c_ack),

        // Backend
        .m_addr   (ic_m_addr),
        .m_data_in(ic_m_data_in),
        .m_access (ic_m_access),
        .m_ack    (ic_m_ack),

        // Invalidation from final arbiter (unused, tied off)
        .inval_valid(ic_inval_valid),
        .inval_addr (ic_inval_addr),

        // Coherence sideband from D-cache
        .coh_wr_valid     (coh_wr_valid),
        .coh_wr_addr      (coh_wr_addr),
        .coh_wr_data      (coh_wr_data),
        .coh_wr_bytesel   (coh_wr_bytesel),
        .coh_probe_valid  (coh_probe_valid),
        .coh_probe_addr   (coh_probe_addr),
        .coh_probe_present(coh_probe_present)
    );

    DCache2Way #(.sets(64), .DEBUG(1'b1)) dcache (
        .clk      (clk),
        .reset    (reset),
        .enabled  (1'b1),

        // Frontend
        .c_addr      (dc_c_addr),
        .c_data_in   (dc_c_data_in),
        .c_data_out  (dc_c_data_out),
        .c_access    (dc_c_access),
        .c_ack       (dc_c_ack),
        .c_wr_en     (dc_c_wr_en),
        .c_bytesel   (dc_c_bytesel),

        // Backend
        .m_addr      (dc_m_addr),
        .m_data_in   (dc_m_data_in),
        .m_data_out  (dc_m_data_out),
        .m_access    (dc_m_access),
        .m_ack       (dc_m_ack),
        .m_wr_en     (dc_m_wr_en),
        .m_bytesel   (dc_m_bytesel),

        // Coherence sideband to I-cache
        .coh_wr_valid     (coh_wr_valid),
        .coh_wr_addr      (coh_wr_addr),
        .coh_wr_data      (coh_wr_data),
        .coh_wr_bytesel   (coh_wr_bytesel),
        .coh_probe_valid  (coh_probe_valid),
        .coh_probe_addr   (coh_probe_addr),
        .coh_probe_present(coh_probe_present)
    );

    // Simple shared SDRAM model for both caches (1-cycle latency)

    always_ff @(posedge clk) begin
        if (reset) begin
            ic_m_ack <= 1'b0;
            dc_m_ack <= 1'b0;
            ic_m_data_in <= 16'h0000;
            dc_m_data_in <= 16'h0000;
        end else begin
            // I-cache (read-only)
            ic_m_ack <= ic_m_access;
            if (ic_m_access)
                ic_m_data_in <= memory[ic_m_addr[12:1]];

            // D-cache (read/write)
            dc_m_ack <= dc_m_access;
            if (dc_m_access) begin
                if (dc_m_wr_en) begin
                    if (dc_m_bytesel[0])
                        memory[dc_m_addr[12:1]][7:0]  <= dc_m_data_out[7:0];
                    if (dc_m_bytesel[1])
                        memory[dc_m_addr[12:1]][15:8] <= dc_m_data_out[15:8];
                end else begin
                    dc_m_data_in <= memory[dc_m_addr[12:1]];
                end
            end
        end
    end

    // Helper: check result
    task automatic check_result(input [15:0] expected, input [15:0] actual, input string desc);
        begin
            test_count++;
            if (expected === actual) begin
                pass_count++;
                $display("  ✓ PASS: %s (exp=%h, got=%h)", desc, expected, actual);
            end else begin
                fail_count++;
                $display("  ✗ FAIL: %s (exp=%h, got=%h)", desc, expected, actual);
            end
        end
    endtask

    // Coherence sideband debug (only for this focused test)
    always_ff @(posedge clk) begin
        if (coh_probe_valid)
            $display("  [DBG] PROBE addr=%h present=%b", coh_probe_addr, coh_probe_present);
        if (coh_wr_valid)
            $display("  [DBG] COH_WR addr=%h data=%h be=%b", coh_wr_addr, coh_wr_data, coh_wr_bytesel);
    end

    // Test parameters
    logic [19:1] code_addr;
    logic [15:0] data;

    // Helper: single I-cache fetch
    task automatic ic_fetch(input [19:1] addr, output [15:0] data);
        integer cycles;
        begin
            cycles = 0;
            ic_c_addr = addr;
            ic_c_access = 1'b1;
            @(posedge clk);
            while (!ic_c_ack && cycles < 1000) begin
                cycles++;
                @(posedge clk);
            end
            data = ic_c_data_in;
            ic_c_access = 1'b0;
            $display("  [IC] Fetch addr=%h -> data=%h (cycles=%0d)", addr, data, cycles);
        end
    endtask

    // Helper: single D-cache write
    task automatic dc_store(input [19:1] addr, input [15:0] data, input [1:0] be);
        integer cycles;
        begin
            cycles = 0;
            dc_c_addr    = addr;
            dc_c_data_out= data;
            dc_c_bytesel = be;
            dc_c_wr_en   = 1'b1;
            dc_c_access  = 1'b1;
            @(posedge clk);
            while (!dc_c_ack && cycles < 1000) begin
                cycles++;
                @(posedge clk);
            end
            dc_c_access  = 1'b0;
            dc_c_wr_en   = 1'b0;
            $display("  [DC] Store addr=%h data=%h be=%b (cycles=%0d)", addr, data, be, cycles);
        end
    endtask

    // Main test sequence
    initial begin
        $dumpfile("icache_dcache_coh_tb.vcd");
        $dumpvars(0, icache_dcache_coh_tb);

        $display("=============================================================");
        $display("ICache2Way <-> DCache2Way Coherence Sideband Test");
        $display("=============================================================");

        test_count = 0;
        pass_count = 0;
        fail_count = 0;

        // Coherence instrumentation
        $display("[DBG] Starting sideband test: coh_probe_valid / coh_probe_present / coh_wr_valid traces enabled");

        // Init memory
        begin : init_block
            integer i;
            for (i = 0; i < 4096; i = i + 1)
                memory[i] = 16'h0000;
        end

        // Test parameters
        code_addr = 19'h00300;
        memory[code_addr[12:1]] = 16'h1111;  // original code

        // Reset
        reset = 1'b1;
        ic_c_access = 1'b0;
        dc_c_access = 1'b0;
        dc_c_wr_en  = 1'b0;
        ic_inval_valid = 1'b0;
        ic_inval_addr  = 19'h0;
        repeat (5) @(posedge clk);
        reset = 1'b0;
        repeat (5) @(posedge clk);

        // --------------------------------------------------------------------
        // Test 1: I-cache residency + D-cache write-through + I-cache refetch
        // --------------------------------------------------------------------
        $display("\n--- Test 1: D-store to resident I-cache line ---");

        // Step 1: I-cache fetch (brings line into I-cache)
        ic_fetch(code_addr, data);
        check_result(16'h1111, data, "ICache initial fetch");

        // Sanity: backing memory still has original code
        check_result(16'h1111, memory[code_addr[12:1]],
                     "Backing memory initial code");

        // Step 2: D-cache store new code at same address
        dc_store(code_addr, 16'hDEAD, 2'b11);

        // Give time for write-through to update memory and for I-cache
        // to observe coh_wr_* and invalidate residency.
        repeat (20) @(posedge clk);

        // Check backing memory saw the write-through
        check_result(16'hDEAD, memory[code_addr[12:1]],
                     "Backing memory after D-store");

        // Step 3: I-cache fetch again; should see updated code via miss+refill
        ic_fetch(code_addr, data);
        check_result(16'hDEAD, data,
                     "ICache refetch after D-store to resident line");

        // --------------------------------------------------------------------
        // Summary
        // --------------------------------------------------------------------
        $display("\n=============================================================");
        $display("Test Summary");
        $display("=============================================================");
        $display("Total tests : %0d", test_count);
        $display("Passed      : %0d", pass_count);
        $display("Failed      : %0d", fail_count);

        if (fail_count == 0) begin
            $display("\n✓✓✓ ICache/DCache coherence sideband test PASSED ✓✓✓");
            $finish(0);
        end else begin
            $display("\n✗✗✗ ICache/DCache coherence sideband test FAILED ✗✗✗");
            $finish(1);
        end
    end

endmodule
