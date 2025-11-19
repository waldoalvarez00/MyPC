// Simplified test for DCache2Way hit detection
// Single write-miss, fill, write buffer application, then read
`timescale 1ns/1ps
`default_nettype none

module dcache2way_simple_test;
    localparam SETS = 4;

    logic clk = 0;
    logic reset = 0;
    always #5 clk = ~clk;

    // CPU side
    logic [19:1] c_addr;
    logic [15:0] c_data_in;
    logic [15:0] c_data_out;
    logic        c_access;
    logic        c_ack;
    logic        c_wr_en;
    logic [1:0]  c_bytesel;

    // Memory side
    logic [19:1] m_addr;
    logic [15:0] m_data_in;
    logic [15:0] m_data_out;
    logic        m_access;
    logic        m_ack;
    logic        m_wr_en;
    logic [1:0]  m_bytesel;

    // Simple SDRAM model
    logic [15:0] mem [0:2047];

    DCache2Way #(.sets(SETS), .DEBUG(1'b1)) dut (
        .clk(clk),
        .reset(reset),
        .enabled(1'b1),
        .c_addr(c_addr),
        .c_data_in(c_data_in),
        .c_data_out(c_data_out),
        .c_access(c_access),
        .c_ack(c_ack),
        .c_wr_en(c_wr_en),
        .c_bytesel(c_bytesel),
        .m_addr(m_addr),
        .m_data_in(m_data_in),
        .m_data_out(m_data_out),
        .m_access(m_access),
        .m_ack(m_ack),
        .m_wr_en(m_wr_en),
        .m_bytesel(m_bytesel),
        .coh_wr_valid(),
        .coh_wr_addr(),
        .coh_wr_data(),
        .coh_wr_bytesel(),
        .coh_probe_valid(),
        .coh_probe_addr(),
        .coh_probe_present(1'b0)
    );

    // Memory model: 1-cycle ack
    always_ff @(posedge clk) begin
        m_ack <= 1'b0;
        if (reset) begin
            m_ack <= 1'b0;
            m_data_in <= 16'h0000;
        end else if (m_access) begin
            m_ack <= 1'b1;
            if (m_wr_en) begin
                if (m_bytesel[0]) mem[m_addr[11:1]][7:0]  <= m_data_out[7:0];
                if (m_bytesel[1]) mem[m_addr[11:1]][15:8] <= m_data_out[15:8];
            end else begin
                m_data_in <= mem[m_addr[11:1]];
            end
        end
    end

    task automatic cpu_store(input [19:1] addr, input [15:0] data, input [1:0] be);
        integer t;
        begin
            c_addr     = addr;
            c_data_out = data;
            c_bytesel  = be;
            c_wr_en    = 1'b1;
            c_access   = 1'b1;
            t = 0;
            @(posedge clk);
            while (!c_ack && t < 50) begin t++; @(posedge clk); end
            c_access   = 1'b0;
            c_wr_en    = 1'b0;
            repeat(1) @(posedge clk);
        end
    endtask

    task automatic cpu_load(input [19:1] addr, output [15:0] data);
        integer t;
        begin
            c_addr    = addr;
            c_wr_en   = 1'b0;
            c_bytesel = 2'b11;
            c_access  = 1'b1;
            t = 0;
            @(posedge clk);
            while (!c_ack && t < 50) begin t++; @(posedge clk); end
            data = c_data_in;
            c_access = 1'b0;
            repeat(1) @(posedge clk);
        end
    endtask

    integer failures;
    localparam [19:1] ADDR = 19'h00020;  // Index 2, word 0

    initial begin
        integer i;
        reg [15:0] r;
        failures = 0;

        // Init memory
        for (i = 0; i < 2048; i = i + 1) mem[i] = 16'hAAAA;

        reset = 1'b1;
        c_access = 1'b0;
        c_wr_en = 1'b0;
        c_bytesel = 2'b11;
        c_addr = 19'h00000;
        c_data_out = 16'h0000;
        repeat(4) @(posedge clk);
        reset = 1'b0;
        repeat(4) @(posedge clk);

        $display("=== Simplified DCache2Way Test ===");

        // Step 1: Single write-miss to trigger fill
        $display("\n--- Step 1: Write-miss to %h (data=0xDEAD) ---", ADDR);
        cpu_store(ADDR, 16'hDEAD, 2'b11);

        // Wait for fill + wbuf application to complete (8 words fill + 8 words apply = 16 cycles minimum)
        repeat(25) @(posedge clk);

        // Step 2: Read back the same address - should hit
        $display("\n--- Step 2: Read from %h (expect 0xDEAD) ---", ADDR);
        cpu_load(ADDR, r);

        if (r != 16'hDEAD) begin
            $display("FAIL: Read expected DEAD, got %h", r);
            failures++;
        end else begin
            $display("PASS: Read returned correct value DEAD");
        end

        // Summary
        if (failures == 0) begin
            $display("\n✓ PASSED: Simple hit detection test");
            $finish(0);
        end else begin
            $display("\n✗ FAILED: %0d issues", failures);
            $finish(1);
        end
    end
endmodule

`default_nettype wire
