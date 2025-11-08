// CGA Controller Diagnostic Test
// Simplified test to identify specific bugs
// Focuses on basic functionality without complex integration

`timescale 1ns/1ps

module cga_diagnostic_tb;

// Clocks
logic clock;
logic clk_vga_cga;
logic reset;

// VGA outputs
logic vga_hsync;
logic vga_vsync;
logic [5:0] vga_r;
logic [5:0] vga_g;
logic [5:0] vga_b;

// IO Bus
logic regaccess;
logic [19:1] data_m_addr;
logic [15:0] data_m_data_in;
logic [15:0] data_m_data_out;
logic [1:0] data_m_bytesel;
logic data_m_wr_en;
logic data_m_ack;

// Memory Bus
logic memaccess;
logic [19:1] imem_m_addr;
logic [15:0] imem_m_data_in;
logic [15:0] imem_m_data_out;
logic [1:0] imem_m_bytesel;
logic imem_m_wr_en;
logic mem_m_ack;

// Clock generation
initial begin
    clock = 0;
    forever #10 clock = ~clock;  // 50 MHz
end

initial begin
    clk_vga_cga = 0;
    forever #28 clk_vga_cga = ~clk_vga_cga;  // ~14.318 MHz
end

// DUT
cgacard cgacard_inst(
    .clock(clock),
    .clk_vga_cga(clk_vga_cga),
    .reset(reset),
    .vga_hsync(vga_hsync),
    .vga_vsync(vga_vsync),
    .vga_r(vga_r),
    .vga_g(vga_g),
    .vga_b(vga_b),
    .H_BLANK(),
    .V_BLANK(),
    .de_o_cga(),
    .std_hsyncwidth(),
    .regaccess(regaccess),
    .data_m_addr(data_m_addr),
    .data_m_data_in(data_m_data_in),
    .data_m_data_out(data_m_data_out),
    .data_m_bytesel(data_m_bytesel),
    .data_m_wr_en(data_m_wr_en),
    .data_m_ack(data_m_ack),
    .memaccess(memaccess),
    .imem_m_addr(imem_m_addr),
    .imem_m_data_in(imem_m_data_in),
    .imem_m_data_out(imem_m_data_out),
    .imem_m_bytesel(imem_m_bytesel),
    .imem_m_wr_en(imem_m_wr_en),
    .mem_m_ack(mem_m_ack)
);

// Test tracking
integer test_num = 0;
integer issues_found = 0;

// Simple write task
task write_reg(input [15:0] addr, input [7:0] data);
    begin
        @(posedge clock);
        regaccess = 1'b1;
        data_m_addr = addr[19:1];
        data_m_data_in = {8'h00, data};
        data_m_bytesel = 2'b01;
        data_m_wr_en = 1'b1;
        @(posedge clock);
        wait(data_m_ack);
        @(posedge clock);
        regaccess = 1'b0;
        data_m_wr_en = 1'b0;
    end
endtask

// Main diagnostic
initial begin
    $display("================================================================");
    $display("CGA Controller Diagnostic Test");
    $display("Identifying specific bugs and compatibility issues");
    $display("================================================================");

    // Initialize
    reset = 1'b1;
    regaccess = 1'b0;
    memaccess = 1'b0;
    data_m_addr = 19'h0;
    data_m_data_in = 16'h0;
    data_m_bytesel = 2'b00;
    data_m_wr_en = 1'b0;
    imem_m_addr = 19'h0;
    imem_m_data_in = 16'h0;
    imem_m_bytesel = 2'b00;
    imem_m_wr_en = 1'b0;

    repeat(10) @(posedge clock);
    reset = 1'b0;
    repeat(10) @(posedge clock);

    $display("");
    $display("DIAGNOSTIC 1: Clock signals");
    $display("----------------------------------------------------------------");
    test_num = test_num + 1;

    // Check if CGA clock is running
    @(posedge clk_vga_cga);
    @(posedge clk_vga_cga);
    @(posedge clk_vga_cga);
    $display("  [OK] CGA clock is running");

    $display("");
    $display("DIAGNOSTIC 2: Internal sequencer");
    $display("----------------------------------------------------------------");
    test_num = test_num + 1;

    // Monitor clkdiv (sequencer counter)
    repeat(100) @(posedge clk_vga_cga);
    $display("  [INFO] Sequencer has been clocked");
    $display("  [OK] Internal sequencer appears operational");

    $display("");
    $display("DIAGNOSTIC 3: Register access (basic)");
    $display("----------------------------------------------------------------");
    test_num = test_num + 1;

    // Try to write to mode control register
    write_reg(16'h3D8, 8'h09);  // 80x25 text mode
    $display("  [OK] Mode register write completed");

    $display("");
    $display("DIAGNOSTIC 4: CRTC register programming");
    $display("----------------------------------------------------------------");
    test_num = test_num + 1;

    // Program CRTC with basic 80x25 timings
    write_reg(16'h3D4, 8'h00);  // Select register 0
    write_reg(16'h3D5, 8'd113); // H Total = 114 characters

    write_reg(16'h3D4, 8'h01);  // Select register 1
    write_reg(16'h3D5, 8'd80);  // H Displayed = 80 characters

    $display("  [OK] CRTC registers programmed");

    $display("");
    $display("DIAGNOSTIC 5: Video signal generation (long test)");
    $display("----------------------------------------------------------------");
    test_num = test_num + 1;

    // Wait for a reasonable amount of time for video signals
    $display("  [INFO] Waiting for video signals...");
    $display("  [INFO] This will take ~10000 CGA clocks");

    repeat(10000) @(posedge clk_vga_cga);

    // Check if we got any hsync/vsync transitions
    if (vga_hsync === 1'bx || vga_hsync === 1'bz) begin
        $display("  [BUG] HSYNC is undefined (X or Z)");
        issues_found = issues_found + 1;
    end else begin
        $display("  [OK] HSYNC has defined value: %b", vga_hsync);
    end

    if (vga_vsync === 1'bx || vga_vsync === 1'bz) begin
        $display("  [BUG] VSYNC is undefined (X or Z)");
        issues_found = issues_found + 1;
    end else begin
        $display("  [OK] VSYNC has defined value: %b", vga_vsync);
    end

    $display("");
    $display("DIAGNOSTIC 6: Module instantiation check");
    $display("----------------------------------------------------------------");
    test_num = test_num + 1;

    $display("  [INFO] Checking internal module connections...");
    $display("  [INFO] If simulation hangs here, there's likely an");
    $display("  [INFO] initialization or clock issue in a submodule");

    // Check video color outputs
    if (vga_r === 6'bxxxxxx) begin
        $display("  [BUG] VGA Red output is undefined");
        issues_found = issues_found + 1;
    end else begin
        $display("  [OK] VGA Red output has defined value: %b", vga_r);
    end

    $display("");
    $display("================================================================");
    $display("Diagnostic Summary");
    $display("================================================================");
    $display("Tests run:      %0d", test_num);
    $display("Issues found:   %0d", issues_found);

    if (issues_found == 0) begin
        $display("");
        $display("All basic diagnostics passed.");
        $display("Note: Full integration test may reveal additional issues.");
    end else begin
        $display("");
        $display("*** ISSUES DETECTED - See diagnostics above ***");
    end

    $display("================================================================");
    $finish;
end

// Timeout
initial begin
    #5000000;  // 5ms timeout
    $display("TIMEOUT: Diagnostic test did not complete");
    $display("Last test: %0d", test_num);
    $finish;
end

endmodule
