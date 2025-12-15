// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// KF8237_Bus_Control_Logic
// Data Bus Buffer & Read/Write Control Logic
//
// Written by Kitune-san
//

//============================================================================
//
//  Copyright Waldo Alvarez, 2024
//  https://pipflow.com
//
//  This program is free software; you can redistribute it and/or modify it
//  under the terms of the GNU General Public License as published by the Free
//  Software Foundation; either version 3 of the License, or (at your option)
//  any later version.
//
//  This program is distributed in the hope that it will be useful, but WITHOUT
//  ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
//  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
//  more details.
//
//  You should have received a copy of the GNU General Public License along
//  with this program; if not, write to the Free Software Foundation, Inc.,
//  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
//
//============================================================================

`default_nettype none

module KF8237_Bus_Control_Logic (
    // Bus
    input   wire            clock,
    input   wire            reset,
	 
	 output  reg             bus_ack,

    input   logic           chip_select,
    input   logic           io_read_in,
    input   logic           io_write_in,
    input   logic   [3:0]   address_in,
    input   logic   [7:0]   data_bus_in,

    input   logic           lock_bus_control,

    // Internal Bus
    output  logic   [7:0]   internal_data_bus,

    // -- write
    output  logic           write_command_register,
    output  logic           write_mode_register,
    output  logic           write_request_register,
    output  logic           set_or_reset_mask_register,
    output  logic           write_mask_register,
    output  logic   [3:0]   write_base_and_current_address,
    output  logic   [3:0]   write_base_and_current_word_count,

    // -- software command
    output  logic           clear_byte_pointer,
    output  logic           set_byte_pointer,
    output  logic           master_clear,
    output  logic           clear_mask_register,

    // -- read
    output  logic           read_temporary_register,
    output  logic           read_status_register,
    output  logic   [3:0]   read_current_address,
    output  logic   [3:0]   read_current_word_count
);

    //
    // Internal Signals
    //
    logic           prev_write_enable;
    logic           write_flag;
    logic   [3:0]   stable_address;
    logic           read_flag;
	 
	 // Acknowledge logic
    always_ff @(posedge clock or posedge reset) begin
        if (reset) begin
            bus_ack <= 1'b0;
        end else begin
            // Assert `bus_ack` when a read or write operation is initiated
            if ((io_write_in | io_read_in) & chip_select) begin
                bus_ack <= 1'b1;
            end else begin
                // Reset `bus_ack` in the next clock cycle to indicate completion
                bus_ack <= 1'b0;
            end
        end
    end

    //
    // Write Control
    //
    always_ff @(posedge clock or posedge reset) begin
        if (reset)
            internal_data_bus <= 8'b00000000;
        else if (io_write_in & chip_select)
            internal_data_bus <= data_bus_in;
        
    end

    always_ff @(posedge clock or posedge reset) begin
        if (reset)
            prev_write_enable <= 1'b0;
        else if (!chip_select)
            prev_write_enable <= 1'b0;
        else
            prev_write_enable <= io_write_in | lock_bus_control;
    end
	 
    assign write_flag = prev_write_enable & io_write_in;

    always_ff @(posedge clock or posedge reset) begin
        if (reset)
            stable_address <= 4'b0000;
        else
            stable_address <= address_in;
    end

    // Generate write request flags
    assign  write_command_register                  = write_flag & (stable_address == 4'b1000); // 8
    assign  write_mode_register                     = write_flag & (stable_address == 4'b1011); // B
    assign  write_request_register                  = write_flag & (stable_address == 4'b1001); // 9
    assign  set_or_reset_mask_register              = write_flag & (stable_address == 4'b1010); // A
    assign  write_mask_register                     = write_flag & (stable_address == 4'b1111); // F
	 
    assign  write_base_and_current_address[0]       = write_flag & (stable_address == 4'b0000); // 0
    assign  write_base_and_current_address[1]       = write_flag & (stable_address == 4'b0010); // 2
    assign  write_base_and_current_address[2]       = write_flag & (stable_address == 4'b0100); // 4
    assign  write_base_and_current_address[3]       = write_flag & (stable_address == 4'b0110); // 6
	 
    assign  write_base_and_current_word_count[0]    = write_flag & (stable_address == 4'b0001); // 1
    assign  write_base_and_current_word_count[1]    = write_flag & (stable_address == 4'b0011); // 3
    assign  write_base_and_current_word_count[2]    = write_flag & (stable_address == 4'b0101); // 5
    assign  write_base_and_current_word_count[3]    = write_flag & (stable_address == 4'b0111); // 7

    // Generate software command
    assign  clear_byte_pointer                      = write_flag & (stable_address == 4'b1100); // C
    assign  set_byte_pointer                        = read_flag  & (stable_address == 4'b1100); // C
    assign  master_clear                            = write_flag & (stable_address == 4'b1101); // D
    assign  clear_mask_register                     = write_flag & (stable_address == 4'b1110); // E

    //
    // Read Control
    //
    assign  read_flag = io_read_in & chip_select & lock_bus_control;

    // Generate read request flags
    assign  read_temporary_register                 = read_flag & (address_in == 4'b1101);
    assign  read_status_register                    = read_flag & (address_in == 4'b1000);
    assign  read_current_address[0]                 = read_flag & (address_in == 4'b0000);
    assign  read_current_address[1]                 = read_flag & (address_in == 4'b0010);
    assign  read_current_address[2]                 = read_flag & (address_in == 4'b0100);
    assign  read_current_address[3]                 = read_flag & (address_in == 4'b0110);
    assign  read_current_word_count[0]              = read_flag & (address_in == 4'b0001);
    assign  read_current_word_count[1]              = read_flag & (address_in == 4'b0011);
    assign  read_current_word_count[2]              = read_flag & (address_in == 4'b0101);
    assign  read_current_word_count[3]              = read_flag & (address_in == 4'b0111);

endmodule

