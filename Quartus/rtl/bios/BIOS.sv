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

`default_nettype none
module BIOS #(parameter depth = 32)
             (input logic clk,
              input logic cs,
              input logic data_m_access,
              output logic data_m_ack,
              input logic [19:1] data_m_addr,
              input logic data_m_wr_en,
              input logic [15:0] data_m_data_in,
              output logic [15:0] data_m_data_out,
              input logic [1:0] data_m_bytesel,

              // Upload interface for BIOS file loading from MiSTer OSD
              input logic        upload_wr_req,
              input logic [13:1] upload_addr,
              input logic [15:0] upload_data,
              input logic [1:0]  upload_bytesel);

// Write enable: Only allow uploads (CPU writes disabled for protection)
wire cpu_wr = 1'b0;  // CPU writes permanently disabled
wire wr_en = cpu_wr | upload_wr_req;

// Address mux: CPU address OR upload address
wire [$clog2(depth):1] ram_addr = upload_wr_req ? upload_addr[$clog2(depth):1] : data_m_addr[$clog2(depth):1];

// Data mux: CPU data OR upload data
wire [15:0] ram_data = upload_wr_req ? upload_data : data_m_data_in;

// Bytesel mux
wire [1:0] ram_bytesel = upload_wr_req ? upload_bytesel : data_m_bytesel;

wire [15:0] q;

assign data_m_data_out = cs & data_m_access ? q : 16'b0;

logic condition_met, condition_met_d; // Signals to detect rising edge of the condition

always_ff @(posedge clk) begin
    // Capture condition in current and previous clock cycles
    condition_met <= cs & data_m_access;
    condition_met_d <= condition_met;
    
    // Assert ack only in the cycle following the condition becoming true
    data_m_ack <= condition_met & ~condition_met_d;
end







`ifdef SIMULATION
// Simulation model for altsyncram
reg [15:0] mem [0:depth-1];
reg [15:0] q_reg;

assign q = q_reg;

always_ff @(posedge clk) begin
    // Read (unregistered output)
    q_reg <= mem[ram_addr];

    // Write with byte enables
    if (wr_en) begin
        if (ram_bytesel[0])
            mem[ram_addr][7:0] <= ram_data[7:0];
        if (ram_bytesel[1])
            mem[ram_addr][15:8] <= ram_data[15:8];
    end
end

// Initialize memory to zero for simulation
initial begin
    integer i;
    for (i = 0; i < depth; i = i + 1)
        mem[i] = 16'h0000;
end

`else
// Altera FPGA implementation
/*
always_ff @(posedge clk)
    data_m_ack <= cs & data_m_access;
	*/

altsyncram	altsyncram_component(.address_a(ram_addr),
                                     .byteena_a(ram_bytesel),
                                     .clock0(clk),
                                     .data_a(ram_data),
                                     .wren_a(wr_en),
                                     .q_a(q),
                                     .aclr0(1'b0),
                                     .aclr1(1'b0),
                                     .address_b(1'b1),
                                     .addressstall_a(1'b0),
                                     .addressstall_b(1'b0),
                                     .byteena_b(1'b1),
                                     .clock1(1'b1),
                                     .clocken0(1'b1),
                                     .clocken1(1'b1),
                                     .clocken2(1'b1),
                                     .clocken3(1'b1),
                                     .data_b(1'b1),
                                     .eccstatus(),
                                     .q_b(),
                                     .rden_a(1'b1),
                                     .rden_b(1'b1),
                                     .wren_b(1'b0));
defparam
        altsyncram_component.byte_size = 8,
        altsyncram_component.clock_enable_input_a = "BYPASS",
        altsyncram_component.clock_enable_output_a = "BYPASS",
        altsyncram_component.lpm_hint = "ENABLE_RUNTIME_MOD=NO",
        altsyncram_component.lpm_type = "altsyncram",
        altsyncram_component.numwords_a = depth,
        altsyncram_component.operation_mode = "SINGLE_PORT",
        altsyncram_component.outdata_aclr_a = "NONE",
        altsyncram_component.outdata_reg_a = "UNREGISTERED",
        altsyncram_component.power_up_uninitialized = "FALSE",
        altsyncram_component.read_during_write_mode_port_a = "NEW_DATA_NO_NBE_READ",
        altsyncram_component.widthad_a = $clog2(depth),
        altsyncram_component.width_a = 16,
        altsyncram_component.width_byteena_a = 2,
        altsyncram_component.init_file = "bios.mif";
`endif

endmodule
