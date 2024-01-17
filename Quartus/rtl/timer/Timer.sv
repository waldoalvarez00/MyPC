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


This Verilog code defines a module named Timer, which appears to be a part of a larger digital system, possibly an FPGA or ASIC design. The module interfaces with external components or systems through various input and output signals and incorporates two instances of a TimerUnit module, which we discussed earlier. Let's break down the key components:

Module Declaration
Timer: The module name.
Inputs: Includes the system clock (clk), reset signal (reset), a timer clock (pit_clk), and several control signals (cs, data_m_addr, data_m_data_in, data_m_bytesel, data_m_wr_en, data_m_access, speaker_gate_en).
Outputs: Includes data output (data_m_data_out), an acknowledgment signal (data_m_ack), an interrupt signal (intr), and a speaker output (speaker_out).
Internal Signals
pit_clk_sync: A synchronized version of the pit_clk signal.
Access control signals (access_timer0, access_timer2, access_ctrl): Determine which part of the module is being accessed based on control inputs.
ctrl_wr_val, channel: Used for configuring the internal TimerUnit instances.
timer0_count, timer2_count: Outputs from the TimerUnit instances.
Components
BitSync: This component synchronizes the pit_clk signal to the system clock clk. This is important for maintaining timing integrity in digital systems.

Two TimerUnit Instances: The module contains two instances of the TimerUnit module (Timer0 and Timer2). Each instance is configured separately and has distinct functions:

Timer0 is configured for general timing purposes and its output is connected to the intr (interrupt) signal.

Timer2 is configured for audio or speaker-related timing, with its output connected to speaker_out.

Functional Logic

The module reads and writes data to the TimerUnit instances based on the control signals. It uses access_timer0, access_timer2, and access_ctrl to determine which TimerUnit to interact with and how to configure or read from it.
Data read from the timer units is placed on the data_m_data_out bus when read operations occur.
The data_m_ack signal is an acknowledgment that is asserted when a valid access to the module occurs.

Operation
The Timer module seems to be part of a system with memory-mapped I/O, where specific addresses (data_m_addr) and byte select signals (data_m_bytesel) are used to interact with the module.
The module supports write operations (configuring the timer units or controlling their operation) and read operations (reading the current timer count).
The timers can be used for generating interrupts (intr) or controlling a speaker (speaker_out), with the latter being gated by speaker_gate_en.
Summary

In summary, this Timer module is a versatile component designed for timing-related functions in a digital system. It can be configured for different purposes (like generating interrupts or controlling a speaker) and interacts with other system components through memory-mapped I/O. The use of two separate timer units allows for flexible and varied timing functionalities within the same module.

*/

/*

Inputs and Output Explained

input logic [1:1] data_m_addr

This is a one-bit input signal named data_m_addr.
Since the bit range is [1:1], it indicates that only one bit is used, effectively making data_m_addr a single-bit value. This is a somewhat unusual way to
 declare a single-bit signal, as typically you might see input logic data_m_addr without the bit range for a single-bit signal.
 
This signal is likely used as part of an addressing scheme to select between different functionalities or registers within the Timer module. In the given code, 
it is used to differentiate between accesses to timer0 and timer2 and also to access the control register.

input logic [15:0] data_m_data_in

This is a 16-bit input bus named data_m_data_in.

It is used to input data into the Timer module, probably for configuration or setting values like reload values for the timers.
The width of 16 bits suggests that the module can accept a relatively wide range of data values, which is typical 
for memory-mapped I/O operations in digital systems.

output logic [15:0] data_m_data_out

This is a 16-bit output bus named data_m_data_out.
It is used to output data from the Timer module. This could be the current count of the timers or some status information.
The 16-bit width matches the input bus, allowing for a consistent data interface size for both reading from and writing to the module.
input logic [1:0] data_m_bytesel

This is a 2-bit input signal named data_m_bytesel.
It is likely used as a byte-select or byte-enable signal. In memory-mapped I/O and bus interfaces, byte-select signals are often 
used to determine which bytes of a wider data bus are active or should be considered valid during a particular data transfer.

For a 16-bit bus, a 2-bit byte-select signal makes sense: it can be used to select between the upper byte ([15:8]), the lower byte ([7:0]), 
or both bytes of the data_m_data_in bus for operations.

Usage in the Module
In the Timer module, these signals are used to control data flow and module configuration. For example, data_m_addr is used in 
conjunction with data_m_bytesel to control which part of the module is accessed and whether the access is for Timer0, Timer2, 
or the control registers. data_m_data_in provides the data for these operations, and data_m_data_out is used to send data back 
to the rest of the system, such as the current timer counts or status information.

The combination of these signals allows for flexible and controlled interaction with the Timer module, 
enabling it to function correctly within a larger digital system, likely involving a CPU or 
microcontroller with a memory-mapped peripheral interface.



*/

`default_nettype none
module Timer(input logic clk,
             input logic reset,
             input logic pit_clk,
             input logic cs,
			 
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
                 .*);

always_ff @(posedge clk)
    if (access_timer0 && !data_m_wr_en)
        data_m_data_out <= {8'b0, timer0_count};
    else if (access_timer2 && !data_m_wr_en)
        data_m_data_out <= {8'b0, timer2_count};
    else
        data_m_data_out <= 16'b0;

always_ff @(posedge clk)
    data_m_ack <= cs & data_m_access;

endmodule
