//============================================================================
//
//  Floppy SD Card Integration Testbench
//  Verifies floppy_disk_manager module and MiSTer HPS integration
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module floppy_sd_integration_tb;

// Clock and reset
reg clk;
reg reset;

// HPS disk image mounting interface
reg [1:0]  img_mounted;
reg [1:0]  img_readonly;
reg [63:0] img_size;

// SD card interface
wire [31:0] sd_lba;
wire [1:0]  sd_rd;
wire [1:0]  sd_wr;
reg  [1:0]  sd_ack;
reg  [8:0]  sd_buff_addr;
reg  [7:0]  sd_buff_dout;
wire [7:0]  sd_buff_din;
wire        sd_buff_wr;

// Floppy controller management interface
reg  [3:0]  mgmt_address;
reg         mgmt_fddn;
reg         mgmt_write;
reg  [15:0] mgmt_writedata;
reg         mgmt_read;
wire [15:0] mgmt_readdata;

// Floppy request interface
reg  [1:0]  floppy_request;
wire [1:0]  wp_status;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;

// DUT instantiation
floppy_disk_manager dut (
    .clk                (clk),
    .reset              (reset),
    .img_mounted        (img_mounted),
    .img_readonly       (img_readonly),
    .img_size           (img_size),
    .sd_lba             (sd_lba),
    .sd_rd              (sd_rd),
    .sd_wr              (sd_wr),
    .sd_ack             (sd_ack),
    .sd_buff_addr       (sd_buff_addr),
    .sd_buff_dout       (sd_buff_dout),
    .sd_buff_din        (sd_buff_din),
    .sd_buff_wr         (sd_buff_wr),
    .mgmt_address       (mgmt_address),
    .mgmt_fddn          (mgmt_fddn),
    .mgmt_write         (mgmt_write),
    .mgmt_writedata     (mgmt_writedata),
    .mgmt_read          (mgmt_read),
    .mgmt_readdata      (mgmt_readdata),
    .floppy_request     (floppy_request),
    .wp_status          (wp_status)
);

// Clock generation: 50 MHz
initial begin
    clk = 0;
    forever #10 clk = ~clk;  // 20ns period = 50 MHz
end

// Test stimulus
initial begin
    $display("================================================================");
    $display("Floppy SD Card Integration Testbench");
    $display("Testing floppy_disk_manager module and MiSTer HPS integration");
    $display("================================================================");
    $display("");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;

    reset = 1;
    img_mounted = 2'b00;
    img_readonly = 2'b00;
    img_size = 64'h0;
    sd_ack = 2'b00;
    sd_buff_addr = 9'h0;
    sd_buff_dout = 8'h0;
    mgmt_address = 4'h0;
    mgmt_fddn = 1'b0;
    mgmt_write = 1'b0;
    mgmt_writedata = 16'h0;
    mgmt_read = 1'b0;
    floppy_request = 2'b00;

    // Wait for reset
    repeat(10) @(posedge clk);
    reset = 0;
    repeat(5) @(posedge clk);

    $display("Test 1: Verify initial reset state");
    test_count++;
    mgmt_fddn = 1'b0;
    mgmt_address = 4'd0;  // Media present register
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata[0] == 1'b0) begin
        $display("  [PASS] Drive A media not present after reset");
        pass_count++;
    end else begin
        $display("  [FAIL] Drive A should not have media after reset (got %b)", mgmt_readdata[0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 2: Mount 1.44MB disk image on drive A");
    test_count++;
    img_size = 64'd1_474_560;  // 1.44MB
    img_readonly = 2'b00;      // Not write protected
    img_mounted = 2'b01;       // Mount on drive A
    @(posedge clk);
    img_mounted = 2'b00;
    @(posedge clk);
    @(posedge clk);

    // Check media present
    mgmt_fddn = 1'b0;
    mgmt_address = 4'd0;
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata[0] == 1'b1) begin
        $display("  [PASS] Drive A media present after mounting");
        pass_count++;
    end else begin
        $display("  [FAIL] Drive A media should be present (got %b)", mgmt_readdata[0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 3: Verify 1.44MB format detection - cylinders");
    test_count++;
    mgmt_address = 4'd2;  // Cylinders register
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata[7:0] == 8'd80) begin
        $display("  [PASS] Detected 80 cylinders for 1.44MB format");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected 80 cylinders, got %d", mgmt_readdata[7:0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 4: Verify 1.44MB format detection - sectors per track");
    test_count++;
    mgmt_address = 4'd3;  // Sectors per track register
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata[7:0] == 8'd18) begin
        $display("  [PASS] Detected 18 sectors per track for 1.44MB format");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected 18 sectors per track, got %d", mgmt_readdata[7:0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 5: Verify 1.44MB format detection - heads");
    test_count++;
    mgmt_address = 4'd5;  // Heads register
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata[1:0] == 2'd2) begin
        $display("  [PASS] Detected 2 heads for 1.44MB format");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected 2 heads, got %d", mgmt_readdata[1:0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 6: Verify 1.44MB format detection - sector count");
    test_count++;
    mgmt_address = 4'd4;  // Sector count register
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata == 16'd2880) begin
        $display("  [PASS] Detected 2880 sectors for 1.44MB format");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected 2880 sectors, got %d", mgmt_readdata);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 7: Verify write protect status");
    test_count++;
    if (wp_status[0] == 1'b0) begin
        $display("  [PASS] Drive A not write protected");
        pass_count++;
    end else begin
        $display("  [FAIL] Drive A should not be write protected");
        fail_count++;
    end
    @(posedge clk);

    $display("");
    $display("Test 8: Mount write-protected 720KB disk on drive B");
    test_count++;
    img_size = 64'd737_280;  // 720KB
    img_readonly = 2'b10;    // Drive B write protected
    img_mounted = 2'b10;     // Mount on drive B
    @(posedge clk);
    img_mounted = 2'b00;
    @(posedge clk);
    @(posedge clk);

    // Check write protect on drive B
    if (wp_status[1] == 1'b1) begin
        $display("  [PASS] Drive B is write protected");
        pass_count++;
    end else begin
        $display("  [FAIL] Drive B should be write protected");
        fail_count++;
    end
    @(posedge clk);

    $display("");
    $display("Test 9: Verify 720KB format detection - cylinders");
    test_count++;
    mgmt_fddn = 1'b1;  // Select drive B
    mgmt_address = 4'd2;
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata[7:0] == 8'd80) begin
        $display("  [PASS] Detected 80 cylinders for 720KB format");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected 80 cylinders, got %d", mgmt_readdata[7:0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 10: Verify 720KB format detection - sectors per track");
    test_count++;
    mgmt_address = 4'd3;
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata[7:0] == 8'd9) begin
        $display("  [PASS] Detected 9 sectors per track for 720KB format");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected 9 sectors per track, got %d", mgmt_readdata[7:0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 11: Verify 720KB format detection - sector count");
    test_count++;
    mgmt_address = 4'd4;
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata == 16'd1440) begin
        $display("  [PASS] Detected 1440 sectors for 720KB format");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected 1440 sectors, got %d", mgmt_readdata);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 12: Test manual management write - change cylinders");
    test_count++;
    mgmt_fddn = 1'b0;  // Drive A
    mgmt_address = 4'd2;
    mgmt_writedata = 16'd40;  // Change to 40 cylinders
    mgmt_write = 1'b1;
    @(posedge clk);
    mgmt_write = 1'b0;
    @(posedge clk);

    // Read back
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata[7:0] == 8'd40) begin
        $display("  [PASS] Management write updated cylinders to 40");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected 40 cylinders after write, got %d", mgmt_readdata[7:0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 13: Verify 360KB format detection");
    test_count++;
    img_size = 64'd368_640;  // 360KB
    img_readonly = 2'b00;
    img_mounted = 2'b01;     // Mount on drive A
    @(posedge clk);
    img_mounted = 2'b00;
    @(posedge clk);
    @(posedge clk);

    mgmt_fddn = 1'b0;
    mgmt_address = 4'd2;  // Cylinders
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata[7:0] == 8'd40) begin
        $display("  [PASS] Detected 40 cylinders for 360KB format");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected 40 cylinders, got %d", mgmt_readdata[7:0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 14: Verify 360KB sectors per track");
    test_count++;
    mgmt_address = 4'd3;
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata[7:0] == 8'd9) begin
        $display("  [PASS] Detected 9 sectors per track for 360KB format");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected 9 sectors per track, got %d", mgmt_readdata[7:0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 15: Verify 1.2MB format detection");
    test_count++;
    img_size = 64'd1_228_800;  // 1.2MB
    img_readonly = 2'b00;
    img_mounted = 2'b01;
    @(posedge clk);
    img_mounted = 2'b00;
    @(posedge clk);
    @(posedge clk);

    mgmt_address = 4'd3;  // Sectors per track
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata[7:0] == 8'd15) begin
        $display("  [PASS] Detected 15 sectors per track for 1.2MB format");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected 15 sectors per track, got %d", mgmt_readdata[7:0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 16: Verify 2.88MB format detection");
    test_count++;
    img_size = 64'd2_949_120;  // 2.88MB
    img_readonly = 2'b00;
    img_mounted = 2'b01;
    @(posedge clk);
    img_mounted = 2'b00;
    @(posedge clk);
    @(posedge clk);

    mgmt_address = 4'd3;  // Sectors per track
    mgmt_read = 1'b1;
    @(posedge clk);
    @(posedge clk);
    if (mgmt_readdata[7:0] == 8'd36) begin
        $display("  [PASS] Detected 36 sectors per track for 2.88MB format");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected 36 sectors per track, got %d", mgmt_readdata[7:0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

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
    $dumpfile("floppy_sd_integration_tb.vcd");
    $dumpvars(0, floppy_sd_integration_tb);
end

endmodule

`default_nettype wire
