// Copyright Jamie Iles, 2017
//
// This file is part of s80x86.
//
// s80x86 is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// s80x86 is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with s80x86.  If not, see <http://www.gnu.org/licenses/>.




/*

pit_clk_sync: A synchronized version of the pit_clk signal.

BitSync: This component synchronizes the pit_clk signal to the system clock clk. 

Two TimerUnit Instances: The module contains two instances of the TimerUnit module (Timer0 and Timer2). 
Each instance is configured separately and has distinct functions:

Timer0 is configured for general timing purposes and its output is connected to the intr (interrupt) signal.

Timer2 is configured for audio or speaker-related timing, with its output connected to speaker_out.



Inputs and Output Explained

input logic [1:1] data_m_addr

This is a one-bit input signal named data_m_addr.
Since the bit range is [1:1], it indicates that only one bit is used


This signal is used to select between different functionalities or registers within the Timer module. 
It is used to differentiate between accesses to timer0 and timer2 and also to access the control register.

input logic [15:0] data_m_data_in

This is a 16-bit input bus named data_m_data_in.

It is used to input data into the Timer module, probably for configuration or setting 
values like reload values for the timers.

output logic [15:0] data_m_data_out

This is a 16-bit output bus named data_m_data_out.
It is used to output data from the Timer module. This could be the current count of the timers or some status information.
The 16-bit width matches the input bus, allowing for a consistent data interface size for both reading from and writing to the module.


input logic [1:0] data_m_bytesel

This is a 2-bit input signal named data_m_bytesel.
It is used as a byte-select or byte-enable signal.

Usage in the Module
In the Timer module, these signals are used to control data flow and module configuration. For example, data_m_addr is used in 
conjunction with data_m_bytesel to control which part of the module is accessed and whether the access is for Timer0, Timer2, 
or the control registers. data_m_data_in provides the data for these operations, and data_m_data_out is used to send data back 
to the rest of the system, such as the current timer counts or status information.






PIT Channels and Their Uses


Channel 0: Used for system timing purposes, like generating interrupts for the system clock.
Channel 1: Originally used in the PC for dynamic RAM refresh, but often not used or available in later models.
Channel 2: Connected to the PC speaker, can be used for sound generation or as a general-purpose timer.

I/O Ports for the 8253/8254 PIT

0x40: Control register for Channel 0
0x41: Control register for Channel 1
0x42: Control register for Channel 2

0x43: Mode/Command register, used to set the operation mode of the counters.


Programming the PIT

Select the Counter and Mode: First, you need to write a control word to the Mode/Command register
 (0x43) to select the counter you want to configure and the mode it should operate in. The control 
 word is structured as follows:

Bits 6-7: Select the counter (00 for Channel 0, 01 for Channel 1, 10 for Channel 2).
Bits 4-5: Select the access mode (latch count, low byte only, high byte only, low byte/high byte).
Bits 1-3: Select the operating mode (e.g., rate generator, square wave generator).

Bit 0: Select the binary (0) or BCD (1) counting mode.
Set the Count Value: After configuring the mode and counter, you need to write the count value to 
the counter's register. For modes where you set both the low byte and high byte (like the low 
byte/high byte access mode), you write the low byte first, then the high byte.

For example, to program Channel 2 to generate a square wave, you might do the following:

Write the control word to 0x43 to select Channel 2, low byte/high byte mode, and square wave mode.
Write the low byte of the count to 0x42.
Write the high byte of the count to 0x42.

*/


`default_nettype none
module Timer(input logic clk,
             input logic reset,
             input logic pit_clk,
				 
             input logic cs, // Enabled when io and addr == 4Xh (40h - 43h)
			 
             input  logic  [1:1]  data_m_addr,
				 
             input  logic  [15:0] data_m_data_in,
             output logic  [15:0] data_m_data_out,
             input  logic  [1:0]  data_m_bytesel,
			 
             input logic data_m_wr_en,
             input logic data_m_access,
			 
             output logic data_m_ack,
			 
             output logic intr,
             output logic speaker_out,
			 
             input logic speaker_gate_en);

wire pit_clk_sync;

wire access_timer0 = cs & data_m_access & ~data_m_addr[1] & data_m_bytesel[0];
wire access_timer2 = cs & data_m_access & data_m_addr[1] & data_m_bytesel[0];

wire access_ctrl = cs & data_m_access & data_m_addr[1] & data_m_bytesel[1];


// verilator lint_off UNUSED
wire [7:0] ctrl_wr_val = data_m_data_in[15:8];
// verilator lint_on UNUSED


wire [1:0] channel = ctrl_wr_val[7:6];

wire [7:0] timer0_count;
wire [7:0] timer2_count;

BitSync PITSync(.clk(clk),
                .reset(reset),
                .d(pit_clk),
                .q(pit_clk_sync));

TimerUnit Timer0(.pit_clk(pit_clk_sync),
                 .reload_in(data_m_data_in[7:0]),
                 .load(access_timer0 & data_m_wr_en),
                 .rw_in(ctrl_wr_val[5:4]),
                 .mode_in(ctrl_wr_val[2:1]),
                 .configure(access_ctrl && data_m_wr_en && channel == 2'b00 && ctrl_wr_val[5:4] != 2'b00),
                 .latch_count(access_ctrl && data_m_wr_en && channel == 2'b00 && ctrl_wr_val[5:4] == 2'b00),
                 .read_count(access_timer0 && !data_m_wr_en),
                 .count_out(timer0_count),
                 .out(intr),
                 .gate(1'b1),
                 .clk(clk),
                 .reset(reset),					  
                 .*);

TimerUnit Timer2(.pit_clk(pit_clk_sync),
                 .reload_in(data_m_data_in[7:0]),
                 .load(access_timer2 & data_m_wr_en),
                 .rw_in(ctrl_wr_val[5:4]),
                 .mode_in(ctrl_wr_val[2:1]),
                 .configure(access_ctrl && data_m_wr_en && channel == 2'b10 && ctrl_wr_val[5:4] != 2'b00),
                 .latch_count(access_ctrl && data_m_wr_en && channel == 2'b10 && ctrl_wr_val[5:4] == 2'b00),
                 .read_count(access_timer2 && !data_m_wr_en),
                 .count_out(timer2_count),
                 .out(speaker_out),
                 .gate(speaker_gate_en),
                 .clk(clk),
                 .reset(reset),
                 .*);




always_ff @(posedge clk)
    if (access_timer0 && !data_m_wr_en)
        data_m_data_out <= {8'b0, timer0_count}; // Reads timer 0
    else if (access_timer2 && !data_m_wr_en)
        data_m_data_out <= {8'b0, timer2_count}; // Reads Timer 2
    else
        data_m_data_out <= 16'b0;



// Returns ACK to CPU on access

always_ff @(posedge clk)
    data_m_ack <= cs & data_m_access;
endmodule
