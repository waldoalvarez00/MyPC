//============================================================================
//
//  Floppy Disk Manager for MiSTer
//  Handles SD card interface and disk image mounting
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//  This program is free software; you can redistribute it and/or modify it
//  under the terms of the GNU General Public License as published by the Free
//  Software Foundation; either version 3 of the License, or (at your option)
//  any later version.
//
//============================================================================

`default_nettype none

module floppy_disk_manager
(
    input  wire        clk,
    input  wire        reset,

    // HPS disk image mounting interface
    input  wire [1:0]  img_mounted,      // Pulse when disk image mounted (bit 0=drive A, bit 1=drive B)
    input  wire [1:0]  img_readonly,     // Write protect status
    input  wire [63:0] img_size,         // Disk image size in bytes

    // SD card interface
    output logic [31:0] sd_lba,          // Logical block address (sector number)
    output logic [1:0]  sd_rd,           // Read request (bit 0=drive A, bit 1=drive B)
    output logic [1:0]  sd_wr,           // Write request
    input  wire  [1:0]  sd_ack,          // Acknowledge from SD card
    input  wire  [8:0]  sd_buff_addr,    // Buffer address (0-511 for sector)
    input  wire  [7:0]  sd_buff_dout,    // Data from SD card
    output logic [7:0]  sd_buff_din,     // Data to SD card
    output logic        sd_buff_wr,      // Buffer write enable

    // Floppy controller management interface
    input  wire  [3:0]  mgmt_address,    // Management register address
    input  wire         mgmt_fddn,       // Drive select (0=A, 1=B)
    input  wire         mgmt_write,      // Write to management register
    input  wire  [15:0] mgmt_writedata,  // Data to write
    input  wire         mgmt_read,       // Read from management register
    output logic [15:0] mgmt_readdata,   // Data read

    // Floppy request interface
    input  wire  [1:0]  floppy_request,  // bit0=read, bit1=write
    output logic [1:0]  wp_status        // Write protect (bit 0=drive A, bit 1=drive B)
);

// Disk image information per drive
logic [1:0]  media_present;         // Media present flag
logic [1:0]  media_writeprotect;    // Write protect flag
logic [7:0]  media_cylinders[2];    // Number of cylinders
logic [7:0]  media_sectors_per_track[2];  // Sectors per track
logic [15:0] media_sector_count[2]; // Total sector count
logic [1:0]  media_heads[2];        // Number of heads

// Initialize on mount
always @(posedge clk or posedge reset) begin
    if (reset) begin
        media_present <= 2'b00;
        media_writeprotect <= 2'b00;
        media_cylinders[0] <= 8'd0;
        media_cylinders[1] <= 8'd0;
        media_sectors_per_track[0] <= 8'd0;
        media_sectors_per_track[1] <= 8'd0;
        media_sector_count[0] <= 16'd0;
        media_sector_count[1] <= 16'd0;
        media_heads[0] <= 2'd0;
        media_heads[1] <= 2'd0;
    end else begin
        // Handle drive A mounting
        if (img_mounted[0]) begin
            media_present[0] <= (img_size != 64'd0);
            media_writeprotect[0] <= img_readonly[0];

            // Detect floppy format based on image size
            case (img_size[31:0])
                32'd184_320,    // 180KB (40 tracks, 1 side, 9 sectors)
                32'd163_840: begin  // 160KB (40 tracks, 1 side, 8 sectors)
                    media_cylinders[0] <= 8'd40;
                    media_heads[0] <= 2'd1;
                    media_sectors_per_track[0] <= (img_size == 184_320) ? 8'd9 : 8'd8;
                    media_sector_count[0] <= img_size[31:9];  // size / 512
                end

                32'd368_640,    // 360KB (40 tracks, 2 sides, 9 sectors)
                32'd327_680: begin  // 320KB (40 tracks, 2 sides, 8 sectors)
                    media_cylinders[0] <= 8'd40;
                    media_heads[0] <= 2'd2;
                    media_sectors_per_track[0] <= (img_size == 368_640) ? 8'd9 : 8'd8;
                    media_sector_count[0] <= img_size[31:9];
                end

                32'd737_280: begin  // 720KB (80 tracks, 2 sides, 9 sectors)
                    media_cylinders[0] <= 8'd80;
                    media_heads[0] <= 2'd2;
                    media_sectors_per_track[0] <= 8'd9;
                    media_sector_count[0] <= 16'd1440;
                end

                32'd1_228_800: begin  // 1.2MB (80 tracks, 2 sides, 15 sectors)
                    media_cylinders[0] <= 8'd80;
                    media_heads[0] <= 2'd2;
                    media_sectors_per_track[0] <= 8'd15;
                    media_sector_count[0] <= 16'd2400;
                end

                32'd1_474_560: begin  // 1.44MB (80 tracks, 2 sides, 18 sectors) - Most common
                    media_cylinders[0] <= 8'd80;
                    media_heads[0] <= 2'd2;
                    media_sectors_per_track[0] <= 8'd18;
                    media_sector_count[0] <= 16'd2880;
                end

                32'd2_949_120: begin  // 2.88MB (80 tracks, 2 sides, 36 sectors)
                    media_cylinders[0] <= 8'd80;
                    media_heads[0] <= 2'd2;
                    media_sectors_per_track[0] <= 8'd36;
                    media_sector_count[0] <= 16'd5760;
                end

                default: begin  // Unknown size - assume 1.44MB
                    media_cylinders[0] <= 8'd80;
                    media_heads[0] <= 2'd2;
                    media_sectors_per_track[0] <= 8'd18;
                    media_sector_count[0] <= 16'd2880;
                end
            endcase
        end

        // Handle drive B mounting (same logic)
        if (img_mounted[1]) begin
            media_present[1] <= (img_size != 64'd0);
            media_writeprotect[1] <= img_readonly[1];

            case (img_size[31:0])
                32'd184_320, 32'd163_840: begin
                    media_cylinders[1] <= 8'd40;
                    media_heads[1] <= 2'd1;
                    media_sectors_per_track[1] <= (img_size == 184_320) ? 8'd9 : 8'd8;
                    media_sector_count[1] <= img_size[31:9];
                end
                32'd368_640, 32'd327_680: begin
                    media_cylinders[1] <= 8'd40;
                    media_heads[1] <= 2'd2;
                    media_sectors_per_track[1] <= (img_size == 368_640) ? 8'd9 : 8'd8;
                    media_sector_count[1] <= img_size[31:9];
                end
                32'd737_280: begin
                    media_cylinders[1] <= 8'd80;
                    media_heads[1] <= 2'd2;
                    media_sectors_per_track[1] <= 8'd9;
                    media_sector_count[1] <= 16'd1440;
                end
                32'd1_228_800: begin
                    media_cylinders[1] <= 8'd80;
                    media_heads[1] <= 2'd2;
                    media_sectors_per_track[1] <= 8'd15;
                    media_sector_count[1] <= 16'd2400;
                end
                32'd1_474_560: begin
                    media_cylinders[1] <= 8'd80;
                    media_heads[1] <= 2'd2;
                    media_sectors_per_track[1] <= 8'd18;
                    media_sector_count[1] <= 16'd2880;
                end
                32'd2_949_120: begin
                    media_cylinders[1] <= 8'd80;
                    media_heads[1] <= 2'd2;
                    media_sectors_per_track[1] <= 8'd36;
                    media_sector_count[1] <= 16'd5760;
                end
                default: begin
                    media_cylinders[1] <= 8'd80;
                    media_heads[1] <= 2'd2;
                    media_sectors_per_track[1] <= 8'd18;
                    media_sector_count[1] <= 16'd2880;
                end
            endcase
        end

        // Handle manual management writes
        if (mgmt_write) begin
            case (mgmt_address)
                4'd0: media_present[mgmt_fddn] <= mgmt_writedata[0];
                4'd1: media_writeprotect[mgmt_fddn] <= mgmt_writedata[0];
                4'd2: media_cylinders[mgmt_fddn] <= mgmt_writedata[7:0];
                4'd3: media_sectors_per_track[mgmt_fddn] <= mgmt_writedata[7:0];
                4'd4: media_sector_count[mgmt_fddn] <= mgmt_writedata[15:0];
                4'd5: media_heads[mgmt_fddn] <= mgmt_writedata[1:0];
            endcase
        end
    end
end

// Management read interface
always_comb begin
    case (mgmt_address)
        4'd0: mgmt_readdata = {15'b0, media_present[mgmt_fddn]};
        4'd1: mgmt_readdata = {15'b0, media_writeprotect[mgmt_fddn]};
        4'd2: mgmt_readdata = {8'b0, media_cylinders[mgmt_fddn]};
        4'd3: mgmt_readdata = {8'b0, media_sectors_per_track[mgmt_fddn]};
        4'd4: mgmt_readdata = media_sector_count[mgmt_fddn];
        4'd5: mgmt_readdata = {14'b0, media_heads[mgmt_fddn]};
        default: mgmt_readdata = 16'h0001;  // Return 1 for unsupported addresses
    endcase
end

// Output write protect status
assign wp_status = media_writeprotect | img_readonly;

// SD card interface logic
// Note: Full sector buffering logic would go here
// For now, this is a placeholder that passes through floppy requests
always_comb begin
    sd_rd = floppy_request[0] ? (mgmt_fddn ? 2'b10 : 2'b01) : 2'b00;
    sd_wr = floppy_request[1] ? (mgmt_fddn ? 2'b10 : 2'b01) : 2'b00;
    sd_lba = 32'h0;  // Would be calculated from cylinder/head/sector
    sd_buff_din = 8'h00;
    sd_buff_wr = 1'b0;
end

endmodule

`default_nettype wire
