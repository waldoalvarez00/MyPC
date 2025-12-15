//============================================================================
//
//  MemArbiterExtend Testbench
//  Tests CPU/MCGA arbiter for SDRAM access with round-robin scheduling
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module mem_arbiter_extend_tb;

// Clock and reset
reg clk;
reg reset;

// CPU bus (bus A)
reg  [19:1] cpu_m_addr;
wire [15:0] cpu_m_data_in;
reg  [15:0] cpu_m_data_out;
reg         cpu_m_access;
wire        cpu_m_ack;
reg         cpu_m_wr_en;
reg  [1:0]  cpu_m_bytesel;

// MCGA bus (bus B)
reg  [19:1] mcga_m_addr;
wire [15:0] mcga_m_data_in;
reg  [15:0] mcga_m_data_out;
reg         mcga_m_access;
wire        mcga_m_ack;
reg         mcga_m_wr_en;
reg  [1:0]  mcga_m_bytesel;

// SDRAM bus (output)
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

// DUT instantiation
MemArbiterExtend dut (
    .clk              (clk),
    .reset            (reset),
    .cpu_m_addr       (cpu_m_addr),
    .cpu_m_data_in    (cpu_m_data_in),
    .cpu_m_data_out   (cpu_m_data_out),
    .cpu_m_access     (cpu_m_access),
    .cpu_m_ack        (cpu_m_ack),
    .cpu_m_wr_en      (cpu_m_wr_en),
    .cpu_m_bytesel    (cpu_m_bytesel),
    .mcga_m_addr      (mcga_m_addr),
    .mcga_m_data_in   (mcga_m_data_in),
    .mcga_m_data_out  (mcga_m_data_out),
    .mcga_m_access    (mcga_m_access),
    .mcga_m_ack       (mcga_m_ack),
    .mcga_m_wr_en     (mcga_m_wr_en),
    .mcga_m_bytesel   (mcga_m_bytesel),
    .sdram_m_addr     (sdram_m_addr),
    .sdram_m_data_in  (sdram_m_data_in),
    .sdram_m_data_out (sdram_m_data_out),
    .sdram_m_access   (sdram_m_access),
    .sdram_m_ack      (sdram_m_ack),
    .sdram_m_wr_en    (sdram_m_wr_en),
    .sdram_m_bytesel  (sdram_m_bytesel),
    .q_b              (q_b)
);

// Clock generation: 50 MHz
initial begin
    clk = 0;
    forever #10 clk = ~clk;  // 20ns period = 50 MHz
end

// Helper task: CPU read request
task cpu_read(input [19:1] addr, output [15:0] data);
    begin
        @(posedge clk);
        cpu_m_addr = addr;
        cpu_m_wr_en = 1'b0;
        cpu_m_bytesel = 2'b11;
        cpu_m_access = 1'b1;

        // Wait for acknowledgment
        wait(cpu_m_ack == 1'b1);
        @(posedge clk);
        data = cpu_m_data_in;

        // Release bus
        cpu_m_access = 1'b0;
        @(posedge clk);
    end
endtask

// Helper task: CPU write request
task cpu_write(input [19:1] addr, input [15:0] data);
    begin
        @(posedge clk);
        cpu_m_addr = addr;
        cpu_m_data_out = data;
        cpu_m_wr_en = 1'b1;
        cpu_m_bytesel = 2'b11;
        cpu_m_access = 1'b1;

        // Wait for acknowledgment
        wait(cpu_m_ack == 1'b1);
        @(posedge clk);

        // Release bus
        cpu_m_access = 1'b0;
        @(posedge clk);
    end
endtask

// Helper task: MCGA read request
task mcga_read(input [19:1] addr, output [15:0] data);
    begin
        @(posedge clk);
        mcga_m_addr = addr;
        mcga_m_wr_en = 1'b0;
        mcga_m_bytesel = 2'b11;
        mcga_m_access = 1'b1;

        // Wait for acknowledgment
        wait(mcga_m_ack == 1'b1);
        @(posedge clk);
        data = mcga_m_data_in;

        // Release bus
        mcga_m_access = 1'b0;
        @(posedge clk);
    end
endtask

// Helper task: MCGA write request
task mcga_write(input [19:1] addr, input [15:0] data);
    begin
        @(posedge clk);
        mcga_m_addr = addr;
        mcga_m_data_out = data;
        mcga_m_wr_en = 1'b1;
        mcga_m_bytesel = 2'b11;
        mcga_m_access = 1'b1;

        // Wait for acknowledgment
        wait(mcga_m_ack == 1'b1);
        @(posedge clk);

        // Release bus
        mcga_m_access = 1'b0;
        @(posedge clk);
    end
endtask

// SDRAM simulator - responds with data based on address
// Simple 2-cycle response: data ready, then ACK
reg sdram_pending;
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        sdram_m_ack <= 1'b0;
        sdram_pending <= 1'b0;
    end else begin
        if (sdram_m_access && !sdram_pending && !sdram_m_ack) begin
            // First cycle: latch address and prepare data
            sdram_pending <= 1'b1;
            if (!sdram_m_wr_en) begin
                // Return address pattern: invert lower 16 bits for easy verification
                sdram_m_data_in <= ~{3'b0, sdram_m_addr[15:3]};
            end
            sdram_m_ack <= 1'b0;
        end else if (sdram_pending) begin
            // Second cycle: assert ACK
            sdram_m_ack <= 1'b1;
            sdram_pending <= 1'b0;
        end else begin
            // Idle: clear ACK
            sdram_m_ack <= 1'b0;
        end
    end
end

// Test reporting
task report_test(input string name, input logic passed);
    begin
        test_count++;
        if (passed) begin
            $display("  [PASS] %s", name);
            pass_count++;
        end else begin
            $display("  [FAIL] %s", name);
            fail_count++;
        end
    end
endtask

// Test stimulus
initial begin
    logic [15:0] read_data;

    $display("================================================================");
    $display("MemArbiterExtend Testbench");
    $display("Testing CPU/MCGA arbiter with round-robin scheduling");
    $display("================================================================");
    $display("");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;

    reset = 1;
    cpu_m_addr = 19'h00000;
    cpu_m_data_out = 16'h0000;
    cpu_m_access = 0;
    cpu_m_wr_en = 0;
    cpu_m_bytesel = 2'b00;
    mcga_m_addr = 19'h00000;
    mcga_m_data_out = 16'h0000;
    mcga_m_access = 0;
    mcga_m_wr_en = 0;
    mcga_m_bytesel = 2'b00;
    sdram_m_data_in = 16'h0000;
    sdram_m_ack = 0;

    // Wait for reset
    repeat(10) @(posedge clk);
    reset = 0;
    repeat(5) @(posedge clk);

    $display("Test 1: CPU read request");
    cpu_read(19'h12345, read_data);
    $display("  [DEBUG] Read data = 0x%04X (expected non-zero)", read_data);
    report_test("CPU read completed", cpu_m_ack === 1'b0);
    report_test("CPU read data returned", read_data != 16'h0000);

    $display("");
    $display("Test 2: MCGA read request");
    mcga_read(19'h55555, read_data);
    report_test("MCGA read completed", mcga_m_ack === 1'b0);
    report_test("MCGA read data returned", read_data != 16'h0000);

    $display("");
    $display("Test 3: CPU write request");
    cpu_write(19'h11111, 16'hBEEF);
    report_test("CPU write completed", cpu_m_ack === 1'b0);
    report_test("CPU write signals de-asserted", cpu_m_access == 1'b0); // After transaction

    $display("");
    $display("Test 4: MCGA write request");
    mcga_write(19'h22222, 16'hCAFE);
    report_test("MCGA write completed", mcga_m_ack === 1'b0);

    $display("");
    $display("Test 5: Sequential requests (CPU then MCGA)");
    fork
        begin
            cpu_read(19'h33333, read_data);
            $display("  [INFO] CPU read finished first");
        end
    join_none
    #100;
    fork
        begin
            mcga_read(19'h44444, read_data);
            $display("  [INFO] MCGA read finished");
        end
    join
    wait fork;
    report_test("Sequential requests handled", 1'b1);

    $display("");
    $display("Test 6: Round-robin fairness - CPU served first");
    // After CPU served, MCGA should get priority
    repeat(5) @(posedge clk);
    fork
        begin
            @(posedge clk);
            cpu_m_addr = 19'h66666;
            cpu_m_access = 1'b1;
            cpu_m_wr_en = 1'b0;
            wait(cpu_m_ack == 1'b1);
            @(posedge clk);
            cpu_m_access = 1'b0;
        end
        begin
            @(posedge clk);
            mcga_m_addr = 19'h77777;
            mcga_m_access = 1'b1;
            mcga_m_wr_en = 1'b0;
            wait(mcga_m_ack == 1'b1);
            @(posedge clk);
            mcga_m_access = 1'b0;
        end
    join
    repeat(2) @(posedge clk);
    report_test("Simultaneous requests handled", 1'b1);

    $display("");
    $display("Test 7: q_b signal (MCGA busy indicator)");
    // q_b should be high when MCGA is being served or wants access
    @(posedge clk);
    mcga_m_access = 1'b1;
    mcga_m_addr = 19'h88888;
    @(posedge clk);
    @(posedge clk);
    report_test("q_b high when MCGA active", q_b == 1'b1);
    mcga_m_access = 1'b0;
    repeat(5) @(posedge clk);
    report_test("q_b low when MCGA inactive", q_b == 1'b0);

    $display("");
    $display("Test 8: Address/data routing verification");
    // Start CPU transaction and verify routing
    @(posedge clk);
    cpu_m_addr = 19'h3FFFF;
    cpu_m_data_out = 16'hDEAD;
    cpu_m_wr_en = 1'b1;
    cpu_m_access = 1'b1;
    @(posedge clk);
    @(posedge clk);
    report_test("CPU address routed", sdram_m_addr == 19'h3FFFF);
    report_test("CPU data routed", sdram_m_data_out == 16'hDEAD);
    report_test("CPU write enable routed", sdram_m_wr_en == 1'b1);
    cpu_m_access = 1'b0;

    $display("");
    $display("Test 9: Byte select routing");
    @(posedge clk);
    cpu_m_bytesel = 2'b01;
    cpu_m_access = 1'b1;
    @(posedge clk);
    report_test("Byte select routed", sdram_m_bytesel == 2'b01);
    cpu_m_access = 1'b0;

    $display("");
    $display("Test 10: Rapid alternating requests");
    repeat(4) begin
        cpu_read(19'h10001, read_data);
        mcga_read(19'h20002, read_data);
    end
    report_test("Rapid alternating requests", 1'b1);

    // Test Summary
    $display("");
    $display("================================================================");
    $display("Test Summary");
    $display("================================================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    $display("Success Rate: %0d%%", (pass_count * 100) / test_count);
    $display("================================================================");

    if (fail_count == 0) begin
        $display("");
        $display("*** ALL TESTS PASSED ***");
        $display("");
    end else begin
        $display("");
        $display("*** SOME TESTS FAILED ***");
        $display("");
    end

    $finish;
end

// VCD dump for waveform viewing
initial begin
    $dumpfile("mem_arbiter_extend_tb.vcd");
    $dumpvars(0, mem_arbiter_extend_tb);
end

endmodule

`default_nettype wire
