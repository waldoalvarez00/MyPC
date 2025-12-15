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

// Floppy controller CHS interface
reg  [7:0]  floppy_cylinder;
reg         floppy_head;
reg  [7:0]  floppy_sector;
reg         floppy_drive;

// Floppy request interface
reg  [1:0]  floppy_request;
wire [1:0]  wp_status;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;
integer i;

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
    .floppy_cylinder    (floppy_cylinder),
    .floppy_head        (floppy_head),
    .floppy_sector      (floppy_sector),
    .floppy_drive       (floppy_drive),
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
    floppy_cylinder = 8'h0;
    floppy_head = 1'b0;
    floppy_sector = 8'h1;
    floppy_drive = 1'b0;
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

    $display("");
    $display("================================================================");
    $display("CHS to LBA Calculation Tests");
    $display("================================================================");

    // Remount 1.44MB disk for LBA tests
    img_size = 64'd1_474_560;  // 1.44MB: 80 cyl, 2 heads, 18 sectors
    img_readonly = 2'b00;
    img_mounted = 2'b01;
    @(posedge clk);
    img_mounted = 2'b00;
    repeat(5) @(posedge clk);

    $display("");
    $display("Test 17: LBA calculation - First sector (C=0, H=0, S=1)");
    test_count++;
    floppy_cylinder = 8'd0;
    floppy_head = 1'b0;
    floppy_sector = 8'd1;
    floppy_drive = 1'b0;
    floppy_request = 2'b01;  // Read request
    @(posedge clk);
    @(posedge clk);  // Wait for LBA calculation
    @(posedge clk);

    // Read calculated LBA (available after CALC_LBA state)
    mgmt_address = 4'd6;
    mgmt_read = 1'b1;
    @(posedge clk);
    if (mgmt_readdata == 16'd0) begin
        $display("  [PASS] LBA for (0,0,1) = 0");
        pass_count++;
    end else begin
        $display("  [FAIL] LBA for (0,0,1) expected 0, got %d", mgmt_readdata);
        fail_count++;
    end
    mgmt_read = 1'b0;

    // Clear request and simulate SD acknowledge to complete operation
    floppy_request = 2'b00;
    sd_ack = 2'b01;
    repeat(5) @(posedge clk);
    sd_ack = 2'b00;
    repeat(520) @(posedge clk);  // Wait for operation to complete

    $display("");
    $display("Test 18: LBA calculation - Second sector (C=0, H=0, S=2)");
    test_count++;
    floppy_cylinder = 8'd0;
    floppy_head = 1'b0;
    floppy_sector = 8'd2;
    floppy_drive = 1'b0;
    floppy_request = 2'b01;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    mgmt_address = 4'd6;
    mgmt_read = 1'b1;
    @(posedge clk);
    if (mgmt_readdata == 16'd1) begin
        $display("  [PASS] LBA for (0,0,2) = 1");
        pass_count++;
    end else begin
        $display("  [FAIL] LBA for (0,0,2) expected 1, got %d", mgmt_readdata);
        fail_count++;
    end
    mgmt_read = 1'b0;
    floppy_request = 2'b00;
    sd_ack = 2'b01;
    repeat(5) @(posedge clk);
    sd_ack = 2'b00;
    repeat(520) @(posedge clk);

    $display("");
    $display("Test 19: LBA calculation - Head 1, Sector 1 (C=0, H=1, S=1)");
    test_count++;
    floppy_cylinder = 8'd0;
    floppy_head = 1'b1;
    floppy_sector = 8'd1;
    floppy_drive = 1'b0;
    floppy_request = 2'b01;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    mgmt_address = 4'd6;
    mgmt_read = 1'b1;
    @(posedge clk);
    // Formula: LBA = (C * Heads + H) * SPT + (S - 1) = (0*2+1)*18+(1-1) = 18
    if (mgmt_readdata == 16'd18) begin
        $display("  [PASS] LBA for (0,1,1) = 18");
        pass_count++;
    end else begin
        $display("  [FAIL] LBA for (0,1,1) expected 18, got %d", mgmt_readdata);
        fail_count++;
    end
    mgmt_read = 1'b0;
    floppy_request = 2'b00;
    sd_ack = 2'b01;
    repeat(5) @(posedge clk);
    sd_ack = 2'b00;
    repeat(520) @(posedge clk);

    $display("");
    $display("Test 20: LBA calculation - Cylinder 1, Head 0, Sector 1 (C=1, H=0, S=1)");
    test_count++;
    floppy_cylinder = 8'd1;
    floppy_head = 1'b0;
    floppy_sector = 8'd1;
    floppy_drive = 1'b0;
    floppy_request = 2'b01;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    mgmt_address = 4'd6;
    mgmt_read = 1'b1;
    @(posedge clk);
    // Formula: LBA = (1*2+0)*18+(1-1) = 36
    if (mgmt_readdata == 16'd36) begin
        $display("  [PASS] LBA for (1,0,1) = 36");
        pass_count++;
    end else begin
        $display("  [FAIL] LBA for (1,0,1) expected 36, got %d", mgmt_readdata);
        fail_count++;
    end
    mgmt_read = 1'b0;
    floppy_request = 2'b00;
    sd_ack = 2'b01;
    repeat(5) @(posedge clk);
    sd_ack = 2'b00;
    repeat(520) @(posedge clk);

    $display("");
    $display("Test 21: LBA calculation - Last sector (C=79, H=1, S=18)");
    test_count++;
    floppy_cylinder = 8'd79;
    floppy_head = 1'b1;
    floppy_sector = 8'd18;
    floppy_drive = 1'b0;
    floppy_request = 2'b01;
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    mgmt_address = 4'd6;
    mgmt_read = 1'b1;
    @(posedge clk);
    // Formula: LBA = (79*2+1)*18+(18-1) = 159*18+17 = 2862+17 = 2879
    if (mgmt_readdata == 16'd2879) begin
        $display("  [PASS] LBA for (79,1,18) = 2879 (last sector)");
        pass_count++;
    end else begin
        $display("  [FAIL] LBA for (79,1,18) expected 2879, got %d", mgmt_readdata);
        fail_count++;
    end
    mgmt_read = 1'b0;
    floppy_request = 2'b00;
    sd_ack = 2'b01;
    repeat(5) @(posedge clk);
    sd_ack = 2'b00;
    repeat(520) @(posedge clk);

    $display("");
    $display("================================================================");
    $display("SD Card Read/Write Operation Tests");
    $display("================================================================");

    $display("");
    $display("Test 22: SD card read request generation");
    test_count++;
    floppy_cylinder = 8'd0;
    floppy_head = 1'b0;
    floppy_sector = 8'd1;
    floppy_drive = 1'b0;
    floppy_request = 2'b01;  // Read request
    @(posedge clk);  // IDLE → CALC_LBA
    @(posedge clk);  // CALC_LBA → READ_REQUEST
    @(posedge clk);  // READ_REQUEST → READ_WAIT_ACK
    @(posedge clk);  // One more cycle for signals to settle

    if (sd_rd == 2'b01 && sd_lba == 32'd0) begin
        $display("  [PASS] SD read request generated for drive A, LBA=0");
        pass_count++;
    end else begin
        $display("  [FAIL] SD read: expected rd=01 lba=0, got rd=%b lba=%d", sd_rd, sd_lba);
        fail_count++;
    end

    // Simulate SD card acknowledge
    sd_ack = 2'b01;
    @(posedge clk);
    @(posedge clk);
    sd_ack = 2'b00;
    floppy_request = 2'b00;

    // Wait for state machine to complete
    repeat(520) @(posedge clk);

    $display("");
    $display("Test 23: SD card write request generation");
    test_count++;
    floppy_cylinder = 8'd10;
    floppy_head = 1'b1;
    floppy_sector = 8'd5;
    floppy_drive = 1'b0;
    floppy_request = 2'b10;  // Write request
    @(posedge clk);  // IDLE → CALC_LBA
    @(posedge clk);  // CALC_LBA → WRITE_REQUEST
    @(posedge clk);  // WRITE_REQUEST → WRITE_WAIT_ACK
    @(posedge clk);  // One more cycle for signals to settle

    // Expected LBA: (10*2+1)*18+(5-1) = 21*18+4 = 378+4 = 382
    if (sd_wr == 2'b01 && sd_lba == 32'd382) begin
        $display("  [PASS] SD write request generated for drive A, LBA=382");
        pass_count++;
    end else begin
        $display("  [FAIL] SD write: expected wr=01 lba=382, got wr=%b lba=%d", sd_wr, sd_lba);
        fail_count++;
    end

    sd_ack = 2'b01;
    @(posedge clk);
    @(posedge clk);
    sd_ack = 2'b00;
    floppy_request = 2'b00;
    repeat(520) @(posedge clk);

    $display("");
    $display("Test 24: SD card drive B selection");
    test_count++;
    floppy_cylinder = 8'd5;
    floppy_head = 1'b0;
    floppy_sector = 8'd1;
    floppy_drive = 1'b1;  // Drive B
    floppy_request = 2'b01;
    @(posedge clk);  // IDLE → CALC_LBA
    @(posedge clk);  // CALC_LBA → READ_REQUEST
    @(posedge clk);  // READ_REQUEST → READ_WAIT_ACK
    @(posedge clk);  // One more cycle for signals to settle

    // Expected LBA: (5*2+0)*9+(1-1) = 10*9+0 = 90 (Drive B has 720KB: 9 SPT)
    if (sd_rd == 2'b10 && sd_lba == 32'd90) begin
        $display("  [PASS] SD read request generated for drive B, LBA=90");
        pass_count++;
    end else begin
        $display("  [FAIL] SD read drive B: expected rd=10 lba=90, got rd=%b lba=%d", sd_rd, sd_lba);
        fail_count++;
    end

    sd_ack = 2'b10;
    @(posedge clk);
    @(posedge clk);
    sd_ack = 2'b00;
    floppy_request = 2'b00;
    repeat(520) @(posedge clk);

    $display("");
    $display("Test 25: State machine verification");
    test_count++;
    // Check initial state
    mgmt_address = 4'd7;  // State register
    mgmt_read = 1'b1;
    @(posedge clk);
    if (mgmt_readdata[2:0] == 3'd0) begin  // STATE_IDLE
        $display("  [PASS] State machine in IDLE state");
        pass_count++;
    end else begin
        $display("  [FAIL] Expected IDLE state (0), got %d", mgmt_readdata[2:0]);
        fail_count++;
    end
    mgmt_read = 1'b0;
    @(posedge clk);

    $display("");
    $display("Test 26: Buffer write enable during write operation");
    test_count++;
    // Fill buffer with test pattern
    floppy_cylinder = 8'd0;
    floppy_head = 1'b0;
    floppy_sector = 8'd1;
    floppy_drive = 1'b0;
    floppy_request = 2'b10;  // Write request
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);
    @(posedge clk);

    if (sd_buff_wr == 1'b1) begin
        $display("  [PASS] Buffer write enable asserted during write operation");
        pass_count++;
    end else begin
        $display("  [FAIL] Buffer write enable not asserted");
        fail_count++;
    end

    sd_ack = 2'b01;
    @(posedge clk);
    sd_ack = 2'b00;
    floppy_request = 2'b00;
    repeat(520) @(posedge clk);

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
