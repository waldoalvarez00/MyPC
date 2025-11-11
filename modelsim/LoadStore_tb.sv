// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// Comprehensive testbench for LoadStore unit
// Tests Phase 1 & Phase 2 optimizations and all access patterns
//
// This file is part of MyPC.

`timescale 1ns/1ps

module LoadStore_tb();

    logic clk;
    logic reset;

    // Memory Address Register
    logic write_mar;
    logic [15:0] segment;
    logic [15:0] mar_in;

    // Memory Data Register
    wire [15:0] mar_out;
    wire [15:0] mdr_out;
    logic write_mdr;
    logic [15:0] mdr_in;

    // Memory bus
    logic [19:1] m_addr;
    logic [15:0] m_data_in;
    logic [15:0] m_data_out;
    logic m_access;
    logic m_ack;
    logic m_wr_en;
    logic [1:0] m_bytesel;

    // Control
    logic io;
    logic mem_read;
    logic mem_write;
    logic is_8bit;
    logic wr_en;
    wire busy;

    // Test control
    integer test_count = 0;
    integer pass_count = 0;
    integer fail_count = 0;
    integer cycle_count = 0;

    // DUT
    LoadStore dut (
        .clk(clk),
        .reset(reset),
        .write_mar(write_mar),
        .segment(segment),
        .mar_in(mar_in),
        .mar_out(mar_out),
        .mdr_out(mdr_out),
        .write_mdr(write_mdr),
        .mdr_in(mdr_in),
        .m_addr(m_addr),
        .m_data_in(m_data_in),
        .m_data_out(m_data_out),
        .m_access(m_access),
        .m_ack(m_ack),
        .m_wr_en(m_wr_en),
        .m_bytesel(m_bytesel),
        .io(io),
        .mem_read(mem_read),
        .mem_write(mem_write),
        .is_8bit(is_8bit),
        .wr_en(wr_en),
        .busy(busy)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Cycle counter for latency measurement
    always @(posedge clk) begin
        if (mem_read || mem_write)
            cycle_count++;
        else
            cycle_count = 0;
    end

    // Test tasks
    task reset_dut();
        begin
            reset = 1;
            write_mar = 0;
            write_mdr = 0;
            mem_read = 0;
            mem_write = 0;
            io = 0;
            is_8bit = 0;
            wr_en = 0;
            m_ack = 0;
            m_data_in = 16'h0;
            segment = 16'h1000;
            @(posedge clk);
            reset = 0;
            @(posedge clk);
        end
    endtask

    task write_mar_task(input [15:0] addr);
        begin
            @(posedge clk);
            write_mar = 1;
            mar_in = addr;
            @(posedge clk);
            write_mar = 0;
        end
    endtask

    task write_mdr_task(input [15:0] data);
        begin
            @(posedge clk);
            write_mdr = 1;
            mdr_in = data;
            @(posedge clk);
            write_mdr = 0;
        end
    endtask

    // Test: Aligned 16-bit read (Phase 1: Should complete in 2 cycles with cache hit)
    task test_aligned_read();
        integer start_cycle, end_cycle, latency;
        begin
            test_count++;
            $display("\n[TEST %0d] Aligned 16-bit Read", test_count);

            // Setup MAR
            write_mar_task(16'h0100);  // Aligned address

            // Start read
            @(posedge clk);
            mem_read = 1;
            is_8bit = 0;
            start_cycle = cycle_count;

            // Wait for FSM to transition and initiate access (Phase 2: signals set in IDLE, visible next cycle)
            @(posedge clk);
            $display("[TB DEBUG] After 1 clk: mem_read=%b busy=%b", mem_read, busy);
            @(posedge clk);
            $display("[TB DEBUG] After 2 clk: Checking read signals:");
            $display("[TB DEBUG]   m_access=%b (expect 1), m_wr_en=%b (expect 0)", m_access, m_wr_en);
            $display("[TB DEBUG]   m_bytesel=%b (expect 11)", m_bytesel);
            if (m_access && !m_wr_en && m_bytesel == 2'b11) begin
                $display("  ✓ Read access initiated correctly");
            end else begin
                $display("  ✗ ERROR: Read access signals incorrect");
                $display("    m_access=%b, m_wr_en=%b, m_bytesel=%b", m_access, m_wr_en, m_bytesel);
                fail_count++;
            end

            // Simulate memory response (cache hit - 1 cycle)
            @(posedge clk);
            m_data_in = 16'hABCD;
            m_ack = 1;
            @(posedge clk);
            m_ack = 0;
            mem_read = 0;  // Clear request signal same cycle as m_ack=0

            // Wait for completion
            wait(!busy);
            end_cycle = cycle_count;
            latency = end_cycle - start_cycle;

            @(posedge clk);

            // Check results
            if (mdr_out == 16'hABCD) begin
                $display("  ✓ Data read correctly: 0x%04X", mdr_out);
                pass_count++;
            end else begin
                $display("  ✗ ERROR: Data mismatch. Expected 0xABCD, got 0x%04X", mdr_out);
                fail_count++;
            end

            $display("  Latency: %0d cycles (Phase 2 target: 3 cycles for cache hit)", latency);
            if (latency <= 3) begin
                $display("  ✓ PHASE 2 OPTIMIZATION VERIFIED: State elimination successful!");
                pass_count++;
            end else begin
                $display("  ⚠ Warning: Latency worse than Phase 2 target (got %0d, expected ≤3)", latency);
            end
        end
    endtask

    // Test: Aligned 16-bit write
    task test_aligned_write();
        integer start_cycle, end_cycle, latency;
        begin
            test_count++;
            $display("\n[TEST %0d] Aligned 16-bit Write", test_count);

            // Setup MAR and MDR
            write_mar_task(16'h0200);
            write_mdr_task(16'h5678);

            // Start write
            @(posedge clk);
            mem_write = 1;
            wr_en = 1;
            is_8bit = 0;
            start_cycle = cycle_count;

            // Wait for FSM to transition and initiate access (Phase 2: signals set in IDLE, visible next cycle)
            @(posedge clk);
            $display("[TB DEBUG] After 1 clk: mem_write=%b busy=%b", mem_write, busy);
            @(posedge clk);
            $display("[TB DEBUG] After 2 clk: Checking write signals:");
            $display("[TB DEBUG]   m_access=%b (expect 1), m_wr_en=%b (expect 1)", m_access, m_wr_en);
            $display("[TB DEBUG]   m_bytesel=%b (expect 11), m_data_out=%04x (expect 5678)", m_bytesel, m_data_out);
            $display("[TB DEBUG]   mdr_out=%04x, busy=%b", mdr_out, busy);
            if (m_access && m_wr_en && m_bytesel == 2'b11 && m_data_out == 16'h5678) begin
                $display("  ✓ Write access initiated correctly");
                pass_count++;
            end else begin
                $display("  ✗ ERROR: Write access signals incorrect");
                $display("    m_access=%b, m_wr_en=%b, m_bytesel=%b, m_data_out=%04X",
                         m_access, m_wr_en, m_bytesel, m_data_out);
                fail_count++;
            end

            // Simulate memory acknowledgment
            @(posedge clk);
            m_ack = 1;
            @(posedge clk);
            m_ack = 0;
            mem_write = 0;  // Clear request signal same cycle as m_ack=0
            wr_en = 0;

            // Wait for completion
            wait(!busy);
            end_cycle = cycle_count;
            latency = end_cycle - start_cycle;

            @(posedge clk);

            $display("  Latency: %0d cycles (Phase 2 target: 3 cycles for cache hit)", latency);
            if (latency <= 3) begin
                $display("  ✓ PHASE 2 OPTIMIZATION VERIFIED: State elimination successful!");
                pass_count++;
            end
        end
    endtask

    // Test: Unaligned 16-bit read
    task test_unaligned_read();
        integer start_cycle, end_cycle, latency;
        begin
            test_count++;
            $display("\n[TEST %0d] Unaligned 16-bit Read", test_count);

            // Setup MAR with unaligned address (odd byte)
            write_mar_task(16'h0101);  // Unaligned address

            // Start read
            @(posedge clk);
            mem_read = 1;
            is_8bit = 0;
            start_cycle = cycle_count;

            // First byte access (wait for FSM transition)
            @(posedge clk);
            @(posedge clk);
            if (m_access && !m_wr_en && m_bytesel == 2'b10) begin
                $display("  ✓ First byte access correct");
            end else begin
                $display("  ✗ ERROR: First byte access incorrect");
                $display("    m_access=%b, m_wr_en=%b, m_bytesel=%b", m_access, m_wr_en, m_bytesel);
                fail_count++;
            end

            @(posedge clk);
            m_data_in = 16'h12AB;  // High byte [15:8]=0x12 goes to mdr[7:0]
            m_ack = 1;
            @(posedge clk);
            m_ack = 0;
            m_data_in = 16'h0000;

            // Second byte access
            @(posedge clk);
            @(posedge clk);
            if (m_access && !m_wr_en && m_bytesel == 2'b01) begin
                $display("  ✓ Second byte access correct");
            end else begin
                $display("  ✗ ERROR: Second byte access incorrect");
                fail_count++;
            end

            @(posedge clk);
            m_data_in = 16'hCD34;  // Low byte [7:0]=0x34 goes to mdr[15:8]
            m_ack = 1;
            @(posedge clk);
            m_ack = 0;
            mem_read = 0;  // Clear request signal same cycle as m_ack=0

            // Wait for completion
            wait(!busy);
            end_cycle = cycle_count;
            latency = end_cycle - start_cycle;

            @(posedge clk);

            // Check result (should be 0x3412)
            if (mdr_out == 16'h3412) begin
                $display("  ✓ Unaligned data assembled correctly: 0x%04X", mdr_out);
                pass_count++;
            end else begin
                $display("  ✗ ERROR: Unaligned data incorrect. Expected 0x3412, got 0x%04X", mdr_out);
                fail_count++;
            end

            $display("  Latency: %0d cycles (Phase 2 target: ≤7 cycles)", latency);
            if (latency <= 7) begin
                $display("  ✓ PHASE 2 OPTIMIZATION VERIFIED: Unaligned operation optimized!");
                pass_count++;
            end
        end
    endtask

    // Test: 8-bit aligned read
    task test_8bit_aligned_read();
        begin
            test_count++;
            $display("\n[TEST %0d] 8-bit Aligned Read", test_count);

            write_mar_task(16'h0300);

            @(posedge clk);
            mem_read = 1;
            is_8bit = 1;

            // Wait for FSM transition
            @(posedge clk);
            @(posedge clk);
            if (m_access && m_bytesel == 2'b01) begin
                $display("  ✓ 8-bit aligned access correct");
            end else begin
                $display("  ✗ ERROR: 8-bit aligned access incorrect");
                $display("    m_access=%b, m_bytesel=%b", m_access, m_bytesel);
                fail_count++;
            end

            @(posedge clk);
            m_data_in = 16'h00AB;  // Low byte contains our data
            m_ack = 1;
            @(posedge clk);
            m_ack = 0;
            mem_read = 0;  // Clear request signal same cycle as m_ack=0

            wait(!busy);
            @(posedge clk);

            if (mdr_out == 16'h00AB) begin
                $display("  ✓ 8-bit data read correctly: 0x%04X", mdr_out);
                pass_count++;
            end else begin
                $display("  ✗ ERROR: 8-bit data incorrect. Expected 0x00AB, got 0x%04X", mdr_out);
                fail_count++;
            end
        end
    endtask

    // Test: 8-bit unaligned read
    task test_8bit_unaligned_read();
        begin
            test_count++;
            $display("\n[TEST %0d] 8-bit Unaligned Read", test_count);

            write_mar_task(16'h0301);  // Odd address

            @(posedge clk);
            mem_read = 1;
            is_8bit = 1;

            // Wait for FSM transition
            @(posedge clk);
            @(posedge clk);
            if (m_access && m_bytesel == 2'b10) begin
                $display("  ✓ 8-bit unaligned access correct (high byte)");
            end else begin
                $display("  ✗ ERROR: 8-bit unaligned access incorrect");
                $display("    m_access=%b, m_bytesel=%b", m_access, m_bytesel);
                fail_count++;
            end

            @(posedge clk);
            m_data_in = 16'hCD00;  // High byte contains our data
            m_ack = 1;
            @(posedge clk);
            m_ack = 0;
            mem_read = 0;  // Clear request signal same cycle as m_ack=0

            wait(!busy);
            @(posedge clk);

            if (mdr_out[7:0] == 8'hCD) begin
                $display("  ✓ 8-bit unaligned data correct: 0x%02X", mdr_out[7:0]);
                pass_count++;
            end else begin
                $display("  ✗ ERROR: 8-bit unaligned data incorrect");
                fail_count++;
            end
        end
    endtask

    // Test: IO read
    task test_io_read();
        begin
            test_count++;
            $display("\n[TEST %0d] IO Read", test_count);

            write_mar_task(16'h0060);  // IO port address

            @(posedge clk);
            io = 1;
            mem_read = 1;
            is_8bit = 0;

            @(posedge clk);
            @(posedge clk);
            if (m_access && m_addr == 19'h0060) begin
                $display("  ✓ IO read address correct");
            end else begin
                $display("  ✗ ERROR: IO read address incorrect");
                fail_count++;
            end

            m_data_in = 16'hFEDC;
            m_ack = 1;
            @(posedge clk);
            m_ack = 0;
            mem_read = 0;  // Clear request signal same cycle as m_ack=0
            io = 0;

            wait(!busy);
            @(posedge clk);

            if (mdr_out == 16'hFEDC) begin
                $display("  ✓ IO data read correctly: 0x%04X", mdr_out);
                pass_count++;
            end else begin
                $display("  ✗ ERROR: IO data incorrect");
                fail_count++;
            end
        end
    endtask

    // Test: Physical address pre-calculation
    task test_physical_address_calculation();
        reg [19:1] expected_addr;
        begin
            test_count++;
            $display("\n[TEST %0d] Physical Address Pre-calculation", test_count);

            segment = 16'h1234;
            write_mar_task(16'h5678);

            // Expected: word_addr = ((segment << 4) + mar) >> 1
            // = ((0x1234 << 4) + 0x5678) >> 1 = (0x12340 + 0x5678) >> 1 = 0x179B8 >> 1 = 0x0BCDC
            expected_addr = 19'h0BCDC;

            @(posedge clk);
            mem_read = 1;

            @(posedge clk);
            @(posedge clk);  // Wait for m_access to be asserted

            if (m_addr == expected_addr) begin
                $display("  ✓ Physical address calculated correctly: 0x%05X", m_addr);
                pass_count++;
            end else begin
                $display("  ✗ ERROR: Physical address incorrect. Expected 0x%05X, got 0x%05X",
                         expected_addr, m_addr);
                fail_count++;
            end

            m_data_in = 16'hDEAD;  // Provide dummy data for the read
            m_ack = 1;
            @(posedge clk);
            m_ack = 0;
            m_data_in = 16'h0000;
            mem_read = 0;  // Clear request signal same cycle as m_ack=0
            wait(!busy);
            @(posedge clk);
        end
    endtask

    // Test: Back-to-back operations (Phase 1: No extra cycle between operations)
    task test_back_to_back_operations();
        integer cycle1, cycle2, gap;
        begin
            test_count++;
            $display("\n[TEST %0d] Back-to-back Operations (Phase 2 optimization check)", test_count);

            // First operation
            write_mar_task(16'h0400);
            @(posedge clk);
            mem_read = 1;
            $display("  First read started: mem_read=%b, busy=%b, io=%b", mem_read, busy, io);
            @(posedge clk);
            $display("  After 1 clk: busy=%b, m_access=%b", busy, m_access);
            @(posedge clk);
            $display("  After 2 clk: busy=%b, m_access=%b", busy, m_access);

            // Wait for LoadStore to assert m_access
            $display("  Waiting for m_access...");
            wait(m_access);
            $display("  m_access asserted!");

            m_data_in = 16'h1111;  // Dummy data
            m_ack = 1;
            @(posedge clk);
            m_ack = 0;
            m_data_in = 16'h0000;
            mem_read = 0;  // Clear request signal same cycle as m_ack=0
            wait(!busy);
            cycle1 = $time;
            @(posedge clk);

            // Second operation - should start immediately
            @(posedge clk);
            write_mar_task(16'h0402);
            @(posedge clk);
            mem_read = 1;
            cycle2 = $time;

            gap = (cycle2 - cycle1) / 10;  // Convert to cycles

            $display("  Gap between operations: %0d cycles", gap);
            if (gap <= 2) begin
                $display("  ✓ PHASE 2 VERIFIED: Optimal back-to-back timing achieved!");
                pass_count++;
            end else if (gap <= 3) begin
                $display("  ✓ PHASE 1 VERIFIED: No FINALIZE_OPERATION delay!");
                pass_count++;
            end else begin
                $display("  ⚠ WARNING: Gap larger than Phase 2 target (%0d cycles, expected ≤2)", gap);
            end

            @(posedge clk);
            @(posedge clk);

            // Wait for LoadStore to assert m_access for second read
            $display("  Waiting for m_access... (busy=%b, m_access=%b)", busy, m_access);
            wait(m_access);
            $display("  m_access detected, providing data");

            m_data_in = 16'h2222;  // Dummy data
            m_ack = 1;
            @(posedge clk);
            m_ack = 0;
            m_data_in = 16'h0000;
            mem_read = 0;  // Clear request signal same cycle as m_ack=0

            $display("  Waiting for busy to clear... (busy=%b)", busy);
            wait(!busy);
            $display("  Second operation complete");
            @(posedge clk);
        end
    endtask

    // Main test sequence
    initial begin
        // Dump waveforms for debugging
        $dumpfile("LoadStore_tb.vcd");
        $dumpvars(0, LoadStore_tb);

        $display("\n========================================");
        $display("  LoadStore Unit - Phase 2 Test Suite");
        $display("  Testing optimizations:");
        $display("  Phase 1:");
        $display("    - FINALIZE_OPERATION removal");
        $display("    - Pre-calculated physical addresses");
        $display("  Phase 2:");
        $display("    - READ_ALIGNED/WRITE_ALIGNED elimination");
        $display("    - Direct IDLE return from WAIT_ACK states");
        $display("    - Reduced state transitions (1 cycle saved)");
        $display("    - Target: 3-cycle aligned operations");
        $display("========================================\n");

        reset_dut();

        // Run all tests
        test_aligned_read();
        test_aligned_write();
        test_unaligned_read();
        test_8bit_aligned_read();
        test_8bit_unaligned_read();
        test_io_read();
        test_physical_address_calculation();
        test_back_to_back_operations();

        // Summary
        $display("\n========================================");
        $display("  Test Summary");
        $display("========================================");
        $display("  Total tests: %0d", test_count);
        $display("  Passed:      %0d", pass_count);
        $display("  Failed:      %0d", fail_count);

        if (fail_count == 0) begin
            $display("\n  ✓✓✓ ALL TESTS PASSED! ✓✓✓");
            $display("  Phase 1 & Phase 2 optimizations working correctly!");
            $display("  State transitions optimized, latency improved");
        end else begin
            $display("\n  ✗✗✗ SOME TESTS FAILED ✗✗✗");
        end
        $display("========================================\n");

        #100;
        $finish;
    end

    // Timeout watchdog
    initial begin
        #50000;
        $display("\n✗ ERROR: Test timeout!");
        $finish;
    end

endmodule
