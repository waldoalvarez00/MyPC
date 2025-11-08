`timescale 1ns / 1ps

/*
 * Testbench for SDRAM Controller
 *
 * Tests the SDRAMController module which manages SDRAM initialization,
 * read/write operations, bank/row management, and auto-refresh.
 */

module sdram_tb();

    // Clock and reset
    logic clk;
    logic reset;

    // Host interface signals
    logic data_m_access;
    logic cs;
    logic [25:1] h_addr;
    logic [15:0] h_wdata;
    logic [15:0] h_rdata;
    logic h_wr_en;
    logic [1:0] h_bytesel;
    logic h_compl;
    logic h_config_done;

    // SDRAM physical interface
    logic s_ras_n;
    logic s_cas_n;
    logic s_wr_en;
    logic [1:0] s_bytesel;
    logic [12:0] s_addr;
    logic s_cs_n;
    logic s_clken;
    wire [15:0] s_data;
    logic [1:0] s_banksel;

    // SDRAM model internal storage
    logic [15:0] sdram_mem[0:65535];  // Simplified SDRAM memory model
    logic [12:0] active_row[0:3];     // Active row for each bank
    logic [3:0] row_active;           // Row active flags for each bank

    // Test control
    integer test_num;
    integer pass_count;
    integer fail_count;

    // Instantiate SDRAM Controller (64MB configuration)
    SDRAMController #(
        .size(64 * 1024 * 1024),
        .clkf(25000000)
    ) uut (
        .clk(clk),
        .reset(reset),
        .data_m_access(data_m_access),
        .cs(cs),
        .h_addr(h_addr),
        .h_wdata(h_wdata),
        .h_rdata(h_rdata),
        .h_wr_en(h_wr_en),
        .h_bytesel(h_bytesel),
        .h_compl(h_compl),
        .h_config_done(h_config_done),
        .s_ras_n(s_ras_n),
        .s_cas_n(s_cas_n),
        .s_wr_en(s_wr_en),
        .s_bytesel(s_bytesel),
        .s_addr(s_addr),
        .s_cs_n(s_cs_n),
        .s_clken(s_clken),
        .s_data(s_data),
        .s_banksel(s_banksel)
    );

    // Bidirectional data bus driver - combinational for proper timing
    // Use pipeline stage 1 to account for command decode delay (CAS latency = 2)
    assign s_data = read_valid_pipe[1] ? read_data_pipe[1] : 16'hzzzz;

    // Clock generation (40ns period = 25 MHz)
    initial begin
        clk = 0;
        forever #20 clk = ~clk;
    end

    // Simple SDRAM behavioral model
    // CAS latency tracking - use pipeline registers
    logic [15:0] read_data_pipe[0:2];  // Pipeline for CAS latency
    logic read_valid_pipe[0:2];        // Valid bits for pipeline

    always_ff @(posedge clk) begin
        // Shift the read pipeline
        read_data_pipe[1] <= read_data_pipe[0];
        read_data_pipe[2] <= read_data_pipe[1];
        read_valid_pipe[1] <= read_valid_pipe[0];
        read_valid_pipe[2] <= read_valid_pipe[1];

        // Debug pipeline state
        if (read_valid_pipe[0] || read_valid_pipe[1] || read_valid_pipe[2])
            $display("  [%0t] SDRAM MODEL: Pipeline [%b %b %b] Data [%h %h %h]", $time,
                     read_valid_pipe[0], read_valid_pipe[1], read_valid_pipe[2],
                     read_data_pipe[0], read_data_pipe[1], read_data_pipe[2]);

        // Clear stage 0 by default
        read_valid_pipe[0] <= 1'b0;

        // Decode SDRAM commands
        if (!s_cs_n) begin
            case ({s_ras_n, s_cas_n, s_wr_en})
                // ACTIVATE (ACTIVE)
                3'b011: begin
                    active_row[s_banksel] <= s_addr;
                    row_active[s_banksel] <= 1'b1;
                    $display("  [%0t] SDRAM MODEL: ACTIVATE bank=%0d, row=0x%h", $time, s_banksel, s_addr);
                end

                // READ
                3'b101: begin
                    if (row_active[s_banksel]) begin
                        // Read from memory (simplified addressing)
                        // Only 64K memory: 2 bits bank + 12 bits row + 2 bits column = 16 bits
                        logic [15:0] addr_index_r;
                        addr_index_r = {s_banksel, active_row[s_banksel][11:0], s_addr[1:0]};
                        read_data_pipe[0] <= sdram_mem[addr_index_r];
                        read_valid_pipe[0] <= 1'b1;
                        $display("  [%0t] SDRAM MODEL: READ cmd bank=%0d, col=0x%h, addr_idx=0x%h, data=0x%h",
                                 $time, s_banksel, s_addr, addr_index_r, sdram_mem[addr_index_r]);
                    end
                end

                // WRITE
                3'b100: begin
                    if (row_active[s_banksel]) begin
                        // Write to memory (simplified addressing)
                        // Only 64K memory: 2 bits bank + 12 bits row + 2 bits column = 16 bits
                        logic [15:0] addr_index_w;
                        logic [15:0] write_data;

                        addr_index_w = {s_banksel, active_row[s_banksel][11:0], s_addr[1:0]};
                        write_data = s_data;

                        $display("  [%0t] SDRAM MODEL: WRITE cmd bank=%0d, col=0x%h, addr_idx=0x%h, data=0x%h, bytesel=0x%b",
                                 $time, s_banksel, s_addr, addr_index_w, write_data, s_bytesel);

                        // Apply byte write enable (s_bytesel is active-low: 0 = write enabled)
                        if (~s_bytesel[0])
                            sdram_mem[addr_index_w][7:0] = write_data[7:0];
                        if (~s_bytesel[1])
                            sdram_mem[addr_index_w][15:8] = write_data[15:8];
                    end
                end

                // PRECHARGE
                3'b010: begin
                    if (s_addr[10]) // Precharge all banks
                        row_active <= 4'b0;
                    else // Precharge single bank
                        row_active[s_banksel] <= 1'b0;
                end

                // AUTO REFRESH
                3'b001: begin
                    row_active <= 4'b0;
                end

                // MODE REGISTER SET, BURST STOP, NOP handled implicitly
                default: ;
            endcase
        end
    end

    // Initialize SDRAM model memory
    initial begin
        for (int i = 0; i < 65536; i++) begin
            sdram_mem[i] = 16'h0000;
        end
        row_active = 4'b0;
        read_valid_pipe[0] = 1'b0;
        read_valid_pipe[1] = 1'b0;
        read_valid_pipe[2] = 1'b0;
    end

    // Task: Wait for initialization to complete
    task wait_init();
        begin
            $display("[%0t] Waiting for SDRAM initialization...", $time);
            wait(h_config_done == 1'b1);
            $display("[%0t] SDRAM initialization complete", $time);
        end
    endtask

    // Task: Perform a write transaction
    task write_sdram(input [25:1] addr, input [15:0] data, input [1:0] bytesel);
        begin
            @(posedge clk);
            #1;  // Small delay to avoid race with always @(posedge clk) blocks
            h_addr = addr;
            h_wdata = data;
            h_wr_en = 1'b1;
            h_bytesel = bytesel;
            cs = 1'b1;
            data_m_access = 1'b1;
            $display("  [%0t] Write to addr=0x%h: data=0x%h, bytesel=0x%h", $time, addr, data, bytesel);

            // Wait for completion
            wait(h_compl == 1'b1);
            @(posedge clk);

            cs = 1'b0;
            data_m_access = 1'b0;
            h_wr_en = 1'b0;
            @(posedge clk);
        end
    endtask

    // Task: Perform a read transaction
    task read_sdram(input [25:1] addr, input [1:0] bytesel, output [15:0] data);
        logic done;
        begin
            done = 0;

            @(posedge clk);
            #1;  // Small delay to avoid race with always @(posedge clk) blocks
            h_addr = addr;
            h_wr_en = 1'b0;
            h_bytesel = bytesel;
            cs = 1'b1;
            data_m_access = 1'b1;

            // Wait for h_compl, sampling at each clock edge
            // h_rdata is only valid for ONE cycle so we must sample synchronously
            while (!done) begin
                @(posedge clk);
                #1;  // Small delay for signal stability
                if (h_compl) begin
                    data = h_rdata;
                    $display("  [%0t] Read from addr=0x%h: data=0x%h", $time, addr, data);
                    done = 1;
                end
            end

            cs = 1'b0;
            data_m_access = 1'b0;
            @(posedge clk);
        end
    endtask

    // Test reporting
    task report_test(input string test_name, input logic pass);
        begin
            if (pass) begin
                $display("✓ Test %0d PASSED: %s", test_num, test_name);
                pass_count++;
            end else begin
                $display("✗ Test %0d FAILED: %s", test_num, test_name);
                fail_count++;
            end
            test_num++;
        end
    endtask

    // Main test sequence
    initial begin
        // Local test variables
        logic [15:0] read_data;
        logic test10_pass;

        // Initialize signals
        reset = 1;
        cs = 0;
        data_m_access = 0;
        h_addr = 0;
        h_wdata = 0;
        h_wr_en = 0;
        h_bytesel = 2'b00;
        test_num = 1;
        pass_count = 0;
        fail_count = 0;

        $display("\n================================================================");
        $display("SDRAM Controller Testbench");
        $display("================================================================\n");

        // Release reset
        #100;
        @(posedge clk);
        reset = 0;

        // Test 1: Wait for initialization
        wait_init();
        report_test("SDRAM initialization", h_config_done == 1'b1);

        // Test 2: Single write operation
        $display("\n[Test %0d] Single write operation", test_num);
        write_sdram(25'h000100, 16'hDEAD, 2'b11);  // Write to address 0x000100 (bytesel=11 = both bytes)
        report_test("Single write operation", h_compl == 1'b0);

        // Test 3: Single read operation
        $display("\n[Test %0d] Single read operation", test_num);
        read_sdram(25'h000100, 2'b11, read_data);  // Read from address 0x000100
        report_test("Single read operation", read_data == 16'hDEAD);

        // Test 4: Write-read different address
        $display("\n[Test %0d] Write-read different address", test_num);
        write_sdram(25'h000200, 16'hBEEF, 2'b11);
        read_sdram(25'h000200, 2'b11, read_data);
        report_test("Write-read different address", read_data == 16'hBEEF);

        // Test 5: Byte-wide write (low byte)
        $display("\n[Test %0d] Byte-wide write (low byte)", test_num);
        write_sdram(25'h000300, 16'h1234, 2'b11);  // First write full word
        write_sdram(25'h000300, 16'hFF56, 2'b01);  // Write only low byte (0x56) - bytesel[0]=1
        read_sdram(25'h000300, 2'b11, read_data);
        report_test("Byte-wide write (low byte)", read_data == 16'h1256);

        // Test 6: Byte-wide write (high byte)
        $display("\n[Test %0d] Byte-wide write (high byte)", test_num);
        write_sdram(25'h000400, 16'h5678, 2'b11);  // First write full word
        write_sdram(25'h000400, 16'hABFF, 2'b10);  // Write only high byte (0xAB) - bytesel[1]=1
        read_sdram(25'h000400, 2'b11, read_data);
        report_test("Byte-wide write (high byte)", read_data == 16'hAB78);

        // Test 7: Same row access (row hit)
        $display("\n[Test %0d] Same row access (row hit)", test_num);
        write_sdram(25'h000500, 16'hCAFE, 2'b11);
        write_sdram(25'h000501, 16'hBABE, 2'b11);  // Same row, next column
        read_sdram(25'h000500, 2'b11, read_data);
        report_test("Same row access - first addr", read_data == 16'hCAFE);
        read_sdram(25'h000501, 2'b11, read_data);
        report_test("Same row access - second addr", read_data == 16'hBABE);

        // Test 8: Different row, same bank (row miss)
        $display("\n[Test %0d] Different row, same bank", test_num);
        write_sdram(25'h002000, 16'h1111, 2'b11);  // Different row
        read_sdram(25'h002000, 2'b11, read_data);
        report_test("Different row, same bank", read_data == 16'h1111);

        // Test 9: Different bank
        $display("\n[Test %0d] Different bank", test_num);
        write_sdram(25'h000800, 16'h2222, 2'b11);  // Bank 0
        write_sdram(25'h001000, 16'h3333, 2'b11);  // Bank 1 (bit 11 changes)
        read_sdram(25'h000800, 2'b11, read_data);
        report_test("Different bank - bank 0", read_data == 16'h2222);
        read_sdram(25'h001000, 2'b11, read_data);
        report_test("Different bank - bank 1", read_data == 16'h3333);

        // Test 10: Multiple sequential writes and reads
        $display("\n[Test %0d] Multiple sequential operations", test_num);
        write_sdram(25'h003000, 16'hAAAA, 2'b11);
        write_sdram(25'h003001, 16'hBBBB, 2'b11);
        write_sdram(25'h003002, 16'hCCCC, 2'b11);
        write_sdram(25'h003003, 16'hDDDD, 2'b11);

        read_sdram(25'h003000, 2'b11, read_data);
        test10_pass = (read_data == 16'hAAAA);
        read_sdram(25'h003001, 2'b11, read_data);
        test10_pass = test10_pass && (read_data == 16'hBBBB);
        read_sdram(25'h003002, 2'b11, read_data);
        test10_pass = test10_pass && (read_data == 16'hCCCC);
        read_sdram(25'h003003, 2'b11, read_data);
        test10_pass = test10_pass && (read_data == 16'hDDDD);

        report_test("Multiple sequential operations", test10_pass);

        // Final summary
        #1000;
        $display("\n================================================================");
        $display("Test Summary");
        $display("================================================================");
        $display("Total Tests: %0d", test_num - 1);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        $display("Success Rate: %0d%%", (pass_count * 100) / (test_num - 1));

        if (fail_count == 0) begin
            $display("\n✓✓✓ SUCCESS: All SDRAM tests passed! ✓✓✓\n");
        end else begin
            $display("\n✗✗✗ FAILURE: %0d test(s) failed ✗✗✗\n", fail_count);
        end

        $display("================================================================\n");
        $finish;
    end

    // Timeout watchdog
    initial begin
        #100000000;  // 100ms timeout
        $display("\n✗✗✗ ERROR: Simulation timeout! ✗✗✗\n");
        $finish;
    end

endmodule
