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

This SystemVerilog (SV) file defines a hardware module named MemArbiter, a memory arbiter used to manage access to 
a shared memory resource between two buses: an instruction bus and a data bus. 


Here's a breakdown of its components and functionality:



I/O Ports:

The module interfaces with two buses: an instruction bus (a) and a data bus (b). Each bus has similar sets of signals:
Address (a_m_addr, b_m_addr): 19-bit addresses for memory access.
Data in (a_m_data_in, b_m_data_in): 16-bit data inputs.
Data out (a_m_data_out, b_m_data_out): 16-bit data outputs.
Access (a_m_access, b_m_access): Signals to request access to memory.
Acknowledge (a_m_ack, b_m_ack): Acknowledgement signals.
Write enable (a_m_wr_en, b_m_wr_en): Write enable signals.
Byte select (a_m_bytesel, b_m_bytesel): Byte selection signals.


Output Bus:

The module also has an output bus (q) with similar signals to manage the actual memory access.

Arbitration Logic:

reg grant_to_b; 
reg grant_active;

These registers keep track of which bus has been granted access and whether the grant is active.
The arbitration logic decides which bus (instruction or data) gets access to the shared memory. 
This is based on the access requests from the two buses and the current state of the arbiter.


Signal Assignments:

The module uses conditional signal assignments to route the correct signals to and from the output bus based on the arbiter's state.
For example, q_m_addr = q_b ? b_m_addr : a_m_addr; decides which address to use based on which bus has been granted access.


State Machine in always_ff Block:

The always_ff block is triggered on the rising edge of the clock or reset.
It contains a simple state machine that controls the grant_active and grant_to_b registers 
based on the current access requests and the acknowledge signal from the memory.

Purpose:

The primary purpose of this module is to ensure that when both the instruction and data buses request access to 
the shared memory, only one of them is granted access at a time, based on a specific arbitration scheme 
(which in this case seems to favor the data bus when both request access simultaneously).

This module is a fundamental component in systems where multiple entities need to access a shared resource (like memory) 
in a controlled manner to avoid conflicts and ensure data integrity.

*/


//`default_nettype none
module MemArbiter(input logic clk,
                  input logic reset,
				  
                  // Instruction bus
                  input logic [19:1] a_m_addr,
                  output logic [15:0] a_m_data_in,
                  input logic [15:0] a_m_data_out,
                  input logic a_m_access,
                  output logic a_m_ack,
                  input logic a_m_wr_en,
                  input logic [1:0] a_m_bytesel,
				  
				  
                  // Data bus
                  input logic [19:1] b_m_addr,
                  output logic [15:0] b_m_data_in,
                  input logic [15:0] b_m_data_out,
                  input logic b_m_access,
                  output logic b_m_ack,
                  input logic b_m_wr_en,
                  input logic [1:0] b_m_bytesel,
				  
				  
                  // Output bus
                  output logic [19:1] q_m_addr,
                  input logic [15:0] q_m_data_in,
                  output logic [15:0] q_m_data_out,
                  output logic q_m_access,
                  input logic q_m_ack,
                  output logic q_m_wr_en,
                  output logic [1:0] q_m_bytesel,
                  output logic q_b);
						
/*
    
	 // Round-robin control
    reg round_robin;

    // Assign outputs based on the current value of round_robin
    assign q_b = round_robin;
    assign q_m_addr = round_robin ? b_m_addr : a_m_addr;
    assign q_m_data_out = round_robin ? b_m_data_out : a_m_data_out;
    assign q_m_access = round_robin ? b_m_access : a_m_access;
    assign q_m_wr_en = round_robin ? b_m_wr_en : a_m_wr_en;
    assign q_m_bytesel = round_robin ? b_m_bytesel : a_m_bytesel;

    assign a_m_data_in = !round_robin ? q_m_data_in : 16'b0;
    assign a_m_ack = !round_robin & q_m_ack;
    assign b_m_data_in = round_robin ? q_m_data_in : 16'b0;
    assign b_m_ack = round_robin & q_m_ack;

    // Arbiter logic with pending request check
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            round_robin <= 1'b0; // Start with the instruction bus
        end else if (q_m_ack) begin
            // Check for pending requests before switching
            if (round_robin) begin
                // If currently serving data bus, switch to instruction bus if it has a request
                if (a_m_access) round_robin <= 1'b0;
            end else begin
                // If currently serving instruction bus, switch to data bus if it has a request
                if (b_m_access) round_robin <= 1'b1;
            end
        end
    end
	 
	 
endmodule*/


reg grant_to_b;
reg grant_active;

assign q_b = (grant_active && grant_to_b) || (!grant_active && b_m_access);

assign q_m_addr = q_b ? b_m_addr : a_m_addr;
assign q_m_data_out = q_b ? b_m_data_out : a_m_data_out;
assign q_m_access = ~q_m_ack & (b_m_access | a_m_access);
assign q_m_wr_en = q_b ? b_m_wr_en : a_m_wr_en;
assign q_m_bytesel = q_b ? b_m_bytesel : a_m_bytesel;

// Register ACK and data outputs to prevent glitches and maintain data stability
logic a_m_ack_reg;
logic b_m_ack_reg;
logic [15:0] a_m_data_in_reg;
logic [15:0] b_m_data_in_reg;

assign a_m_ack = a_m_ack_reg;
assign b_m_ack = b_m_ack_reg;
assign a_m_data_in = a_m_data_in_reg;
assign b_m_data_in = b_m_data_in_reg;

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        grant_active <= 1'b0;
        a_m_ack_reg  <= 1'b0;
        b_m_ack_reg  <= 1'b0;
        a_m_data_in_reg <= 16'b0;
        b_m_data_in_reg <= 16'b0;
    end else begin
        // Update ACK registers
        a_m_ack_reg <= grant_active & ~grant_to_b & q_m_ack;
        b_m_ack_reg <= grant_active & grant_to_b & q_m_ack;

        // Update data registers - latch data when ACK is asserted
        if (grant_active & ~grant_to_b & q_m_ack)
            a_m_data_in_reg <= q_m_data_in;
        if (grant_active & grant_to_b & q_m_ack)
            b_m_data_in_reg <= q_m_data_in;

        // Grant logic
        if (q_m_ack)
            grant_active <= 1'b0;
        else if (!grant_active && (b_m_access || a_m_access)) begin
            grant_active <= 1'b1;
            grant_to_b <= b_m_access;
        end
    end
end

endmodule

