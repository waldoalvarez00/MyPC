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

//==============================================================================
// NOTE: THIS MODULE IS NOT USED IN THE MISTER BUILD
//==============================================================================
// The MiSTer build (mycore.sv) uses KFPS2KB instead of PS2KeyboardController
// for keyboard handling. This module is only compiled when CONFIG_PS2 is
// defined in Top.sv, which is NOT the case for MiSTer.
//
// This module remains in the codebase as:
// - Reference implementation with comprehensive test coverage (21/21 tests)
// - Alternative configuration for non-MiSTer builds
// - Educational value for PS/2 protocol implementation
//
// For MiSTer-specific testing, see: modelsim/kfps2kb_tb.sv
// For this module's tests, see: modelsim/ps2_keyboard_protocol_tb.sv
//
// Key differences from KFPS2KB:
// - CPU register interface (not direct keycode output)
// - 8-entry FIFO for scancode buffering
// - Full PS/2 initialization state machine
// - No MiSTer-specific features (F11/F12 handling)
//==============================================================================

`default_nettype none
module PS2KeyboardController #(parameter clkf=50000000)
                              (input logic clk,
                               input logic reset,
                               // CPU port
                               input logic cs,
                               input logic data_m_access,
                               input logic data_m_wr_en,
                               output logic data_m_ack,
                               output logic [15:0] data_m_data_out,
                               input logic [15:0] data_m_data_in,
                               input logic [1:0] data_m_bytesel,
                               // Interrupt
                               output logic ps2_intr,
                               // PS/2 signals
                               input ps2_clk_in,
					                output ps2_clk_out,
					                input ps2_dat_in,
					                output ps2_dat_out,
					  
                               output logic speaker_data,
                               output logic speaker_gate_en);

wire do_read = data_m_access & cs & ~data_m_wr_en;
wire do_write = data_m_access & cs & data_m_wr_en;

wire [7:0] rx;
wire rx_valid;
wire [7:0] tx;
wire start_tx;
wire tx_busy;
wire tx_complete;
wire error;
wire empty;
wire full;
wire [7:0] fifo_rd_data;
wire [7:0] scancode;
wire scancode_valid;
wire [3:0] count_out;  // Unused but required for Fifo .* connection
wire fifo_wr_en = scancode_valid & ~full & |scancode;
wire fifo_flush = do_write & data_m_bytesel[1] & data_m_data_in[15];

wire fifo_rd_en = cs & data_m_wr_en & data_m_bytesel[1] & data_m_data_in[15] & ~empty;

reg unread_error = 1'b0;

// Internal speaker control signals
logic speaker_data_internal;
logic speaker_gate_en_internal;

// Assign internal signals to outputs
assign speaker_data = speaker_data_internal;
assign speaker_gate_en = speaker_gate_en_internal;

assign ps2_intr = fifo_wr_en;

Fifo    #(.data_width(8),
          .depth(8))
        Fifo(.rd_en(fifo_rd_en),
             .rd_data(fifo_rd_data),
             .wr_en(fifo_wr_en),
             .wr_data(scancode),
             // verilator lint_off PINCONNECTEMPTY
             .nearly_full(),
             // verilator lint_on PINCONNECTEMPTY
             .flush(fifo_flush),
             .*);

wire [7:0] status = {3'b0, ~empty, tx_busy, unread_error, speaker_data_internal, speaker_gate_en_internal};
wire [7:0] data = empty ? 8'b0 : fifo_rd_data;
wire [15:0] read_value = {status, data};

always_ff @(posedge clk) begin
    if (do_read)
        data_m_data_out <= read_value;
    else
        data_m_data_out <= 16'b0;
end

always_ff @(posedge clk)
    data_m_ack <= data_m_access & cs;

always_ff @(posedge clk or posedge reset)
    if (reset)
        unread_error <= 1'b0;
    else if (rx_valid & error)
        unread_error <= 1'b1;
    else if (do_read & data_m_bytesel[1])
        unread_error <= 1'b0;

always_ff @(posedge clk or posedge reset)
    if (reset)
        {speaker_data_internal, speaker_gate_en_internal} <= 2'b0;
    else if (do_write & data_m_bytesel[1])
        {speaker_data_internal, speaker_gate_en_internal} <= {data_m_data_in[9], data_m_data_in[8]};

PS2Host #(.clkf(clkf))
        PS2Host(.*);

KeyboardController KeyboardController(.rx_valid(rx_valid),
                                      .clk(clk),
                                      .reset(reset),
                                      .rx(rx),
                                      .tx(tx),
                                      .start_tx(start_tx),
                                      .tx_complete(tx_complete),
                                      .tx_busy(tx_busy),
                                      .scancode(scancode),
                                      .scancode_valid(scancode_valid));

endmodule
