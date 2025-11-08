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
module KeyboardController(input logic clk,
                          input logic reset,
                          input logic [7:0] rx,
                          input logic rx_valid,
                          output logic [7:0] tx,
                          output logic start_tx,
                          input logic tx_complete,
                          input logic tx_busy,
                          output logic [7:0] scancode,
                          output logic scancode_valid);

reg is_break;
wire [7:0] scancode_out;

assign scancode = is_break ? (8'h80 | scancode_out) : scancode_out;
assign scancode_valid = state == STATE_IDLE &&
                        rx_valid && (scancode_out != 8'hf0 &&
                                     scancode_out != 8'he0 &&
                                     scancode_out != 8'h00);

enum {
    STATE_RESET_START,
    STATE_RESET_WAIT,
    STATE_ENABLE_START,
    STATE_ENABLE_WAIT,
    STATE_IDLE
} state, next_state;

ScancodeTranslator ScancodeTranslator(.scancode_in(rx),
                                      .scancode_out(scancode_out));

always_ff @(posedge clk or posedge reset)
    if (reset)
        is_break <= 1'b0;
    else if (rx_valid)
        is_break <= rx == 8'hf0;

always_comb begin
    case (state)
    STATE_RESET_START: begin
        if (tx_complete)
            next_state = STATE_RESET_WAIT;
        else
            next_state = STATE_RESET_START;
    end
    STATE_RESET_WAIT: begin
        if (rx_valid && rx == 8'haa)
            next_state = STATE_ENABLE_START;
        else
            next_state = STATE_RESET_WAIT;
    end
    STATE_ENABLE_START: begin
        if (tx_complete)
            next_state = STATE_ENABLE_WAIT;
        else
            next_state = STATE_ENABLE_START;
    end
    STATE_ENABLE_WAIT: begin
        if (rx_valid)
            next_state = STATE_IDLE;
        else
            next_state = STATE_ENABLE_WAIT;
    end
    default: next_state = STATE_IDLE;
    endcase

    if (reset)
        next_state = STATE_RESET_START;
end

always_comb begin
    case (state)
    STATE_RESET_START: begin
        start_tx = ~tx_busy & ~tx_complete;
        tx = 8'hff;
    end
    STATE_ENABLE_START: begin
        start_tx = ~tx_busy & ~tx_complete;
        tx = 8'hf4;
    end
    default: begin
        start_tx = 1'b0;
        tx = 8'b0;
    end
    endcase
end

always_ff @(posedge clk)
    state <= next_state;

endmodule
