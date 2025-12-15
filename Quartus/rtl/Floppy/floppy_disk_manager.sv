// Copyright 2025, Waldo Alvarez, https://pipflow.com
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

    // Floppy controller CHS interface
    input  wire  [7:0]  floppy_cylinder,  // Current cylinder (0-79)
    input  wire         floppy_head,      // Current head (0-1)
    input  wire  [7:0]  floppy_sector,    // Current sector (1-based)
    input  wire         floppy_drive,     // Drive selection (0=A, 1=B)

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

// State machine for sector buffering
typedef enum logic [2:0] {
    STATE_IDLE,
    STATE_CALC_LBA,
    STATE_READ_REQUEST,
    STATE_READ_WAIT_ACK,
    STATE_READ_DATA,
    STATE_WRITE_REQUEST,
    STATE_WRITE_WAIT_ACK,
    STATE_WRITE_COMPLETE
} state_t;

state_t state, next_state;

// LBA calculation registers
logic [15:0] lba_temp;
logic [15:0] lba_calculated;
logic [7:0]  calc_cylinder;
logic        calc_head;
logic [7:0]  calc_sector;
logic        calc_drive;

// Sector buffer (512 bytes)
logic [7:0]  sector_buffer[512];
logic [8:0]  buffer_addr;

// SD card control signals
logic [31:0] current_lba;
logic [1:0]  sd_rd_req;
logic [1:0]  sd_wr_req;

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
        4'd6: mgmt_readdata = lba_calculated;  // Debug: expose calculated LBA
        4'd7: mgmt_readdata = {13'b0, state};  // Debug: expose state
        default: mgmt_readdata = 16'h0001;  // Return 1 for unsupported addresses
    endcase
end

// Output write protect status
assign wp_status = media_writeprotect | img_readonly;

//============================================================================
// CHS to LBA Calculation Module
// Formula: LBA = (C * Heads + H) * Sectors_per_track + (S - 1)
//============================================================================

// Capture CHS values when request starts
always @(posedge clk or posedge reset) begin
    if (reset) begin
        calc_cylinder <= 8'd0;
        calc_head <= 1'b0;
        calc_sector <= 8'd0;
        calc_drive <= 1'b0;
    end else if (state == STATE_IDLE && |floppy_request) begin
        calc_cylinder <= floppy_cylinder;
        calc_head <= floppy_head;
        calc_sector <= floppy_sector;
        calc_drive <= floppy_drive;
    end
end

// LBA calculation logic (combinational for single-cycle operation)
// Formula: LBA = (C * Heads + H) * Sectors_per_track + (S - 1)
always_comb begin
    // Step 1: Calculate (Cylinder * Heads + Head)
    if (media_heads[calc_drive] == 2'd2)
        lba_temp = {7'b0, calc_cylinder, 1'b0} + {15'b0, calc_head};  // C*2+H
    else
        lba_temp = {8'b0, calc_cylinder} + {15'b0, calc_head};        // C*1+H

    // Step 2: Calculate temp * Sectors_per_track + (Sector - 1)
    lba_calculated = lba_temp * {8'b0, media_sectors_per_track[calc_drive]} +
                     {8'b0, calc_sector} - 16'd1;
end

//============================================================================
// Sector Buffering State Machine
//============================================================================

// State machine sequential logic
always @(posedge clk or posedge reset) begin
    if (reset)
        state <= STATE_IDLE;
    else
        state <= next_state;
end

// State machine combinational logic
always_comb begin
    next_state = state;

    case (state)
        STATE_IDLE: begin
            if (floppy_request[0]) // Read request
                next_state = STATE_CALC_LBA;
            else if (floppy_request[1]) // Write request
                next_state = STATE_CALC_LBA;
        end

        STATE_CALC_LBA: begin
            // LBA calculation takes one cycle
            if (floppy_request[0])
                next_state = STATE_READ_REQUEST;
            else if (floppy_request[1])
                next_state = STATE_WRITE_REQUEST;
            else
                next_state = STATE_IDLE;
        end

        STATE_READ_REQUEST: begin
            next_state = STATE_READ_WAIT_ACK;
        end

        STATE_READ_WAIT_ACK: begin
            if (sd_ack[calc_drive])
                next_state = STATE_READ_DATA;
        end

        STATE_READ_DATA: begin
            // After acknowledge, return to IDLE
            // (SD card will continue buffering data asynchronously)
            next_state = STATE_IDLE;
        end

        STATE_WRITE_REQUEST: begin
            next_state = STATE_WRITE_WAIT_ACK;
        end

        STATE_WRITE_WAIT_ACK: begin
            if (sd_ack[calc_drive])
                next_state = STATE_WRITE_COMPLETE;
        end

        STATE_WRITE_COMPLETE: begin
            // After acknowledge, return to IDLE
            // (SD card will continue writing data asynchronously)
            next_state = STATE_IDLE;
        end

        default: next_state = STATE_IDLE;
    endcase
end

// Buffer address counter
always @(posedge clk or posedge reset) begin
    if (reset) begin
        buffer_addr <= 9'd0;
    end else begin
        case (state)
            STATE_IDLE, STATE_CALC_LBA: begin
                buffer_addr <= 9'd0;
            end

            STATE_READ_DATA: begin
                if (buffer_addr < 9'd511)
                    buffer_addr <= buffer_addr + 9'd1;
            end

            STATE_WRITE_COMPLETE: begin
                if (buffer_addr < 9'd511)
                    buffer_addr <= buffer_addr + 9'd1;
            end
        endcase
    end
end

// Sector buffer write logic
always @(posedge clk) begin
    if (state == STATE_READ_DATA && buffer_addr == sd_buff_addr) begin
        sector_buffer[buffer_addr] <= sd_buff_dout;
    end
end

// SD card interface outputs
always @(posedge clk or posedge reset) begin
    if (reset) begin
        sd_lba <= 32'd0;
        sd_rd_req <= 2'b00;
        sd_wr_req <= 2'b00;
        current_lba <= 32'd0;
    end else begin
        case (state)
            STATE_IDLE: begin
                sd_rd_req <= 2'b00;
                sd_wr_req <= 2'b00;
            end

            STATE_CALC_LBA: begin
                // Update LBA for next state
                current_lba <= {16'b0, lba_calculated};
            end

            STATE_READ_REQUEST: begin
                sd_lba <= current_lba;
                sd_rd_req <= calc_drive ? 2'b10 : 2'b01;
            end

            STATE_READ_WAIT_ACK: begin
                // Hold request until acknowledged
                sd_lba <= current_lba;
            end

            STATE_READ_DATA: begin
                sd_rd_req <= 2'b00; // Clear request after ack
            end

            STATE_WRITE_REQUEST: begin
                sd_lba <= current_lba;
                sd_wr_req <= calc_drive ? 2'b10 : 2'b01;
            end

            STATE_WRITE_WAIT_ACK: begin
                // Hold request until acknowledged
                sd_lba <= current_lba;
            end

            STATE_WRITE_COMPLETE: begin
                sd_wr_req <= 2'b00; // Clear request after ack
            end
        endcase
    end
end

// SD card buffer data outputs
always_comb begin
    sd_buff_din = sector_buffer[sd_buff_addr];
    sd_buff_wr = (state == STATE_WRITE_REQUEST || state == STATE_WRITE_WAIT_ACK || state == STATE_WRITE_COMPLETE);
end

// Assign SD card request outputs
assign sd_rd = sd_rd_req;
assign sd_wr = sd_wr_req;

endmodule

`default_nettype wire
