// Copyright Jamie Iles, 2018
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

function logic insn_has_modrm;
    input logic [7:0] opcode;

    casez (opcode)
    8'h87: insn_has_modrm = 1'b1;
    8'h8a: insn_has_modrm = 1'b1;
    8'hd2: insn_has_modrm = 1'b1;
    8'h21: insn_has_modrm = 1'b1;
    8'h86: insn_has_modrm = 1'b1;
    8'h19: insn_has_modrm = 1'b1;
    8'hdb: insn_has_modrm = 1'b1;
    8'h84: insn_has_modrm = 1'b1;
    8'hdf: insn_has_modrm = 1'b1;
    8'hd1: insn_has_modrm = 1'b1;
    8'h31: insn_has_modrm = 1'b1;
    8'h89: insn_has_modrm = 1'b1;
    8'h28: insn_has_modrm = 1'b1;
    8'h62: insn_has_modrm = 1'b1;
    8'hd0: insn_has_modrm = 1'b1;
    8'h29: insn_has_modrm = 1'b1;
    8'h2a: insn_has_modrm = 1'b1;
    8'h09: insn_has_modrm = 1'b1;
    8'hd3: insn_has_modrm = 1'b1;
    8'h22: insn_has_modrm = 1'b1;
    8'hd9: insn_has_modrm = 1'b1;
    8'h1b: insn_has_modrm = 1'b1;
    8'h33: insn_has_modrm = 1'b1;
    8'h12: insn_has_modrm = 1'b1;
    8'h1a: insn_has_modrm = 1'b1;
    8'hdd: insn_has_modrm = 1'b1;
    8'hdc: insn_has_modrm = 1'b1;
    8'h6b: insn_has_modrm = 1'b1;
    8'hf6: insn_has_modrm = 1'b1;
    8'h30: insn_has_modrm = 1'b1;
    8'h13: insn_has_modrm = 1'b1;
    8'hfe: insn_has_modrm = 1'b1;
    8'h8e: insn_has_modrm = 1'b1;
    8'h85: insn_has_modrm = 1'b1;
    8'h39: insn_has_modrm = 1'b1;
    8'h20: insn_has_modrm = 1'b1;
    8'h23: insn_has_modrm = 1'b1;
    8'hf7: insn_has_modrm = 1'b1;
    8'h10: insn_has_modrm = 1'b1;
    8'h0a: insn_has_modrm = 1'b1;
    8'h01: insn_has_modrm = 1'b1;
    8'h08: insn_has_modrm = 1'b1;
    8'h81: insn_has_modrm = 1'b1;
    8'h11: insn_has_modrm = 1'b1;
    8'hc7: insn_has_modrm = 1'b1;
    8'h32: insn_has_modrm = 1'b1;
    8'h8d: insn_has_modrm = 1'b1;
    8'h83: insn_has_modrm = 1'b1;
    8'h03: insn_has_modrm = 1'b1;
    8'h8b: insn_has_modrm = 1'b1;
    8'h0b: insn_has_modrm = 1'b1;
    8'hc6: insn_has_modrm = 1'b1;
    8'h3a: insn_has_modrm = 1'b1;
    8'h18: insn_has_modrm = 1'b1;
    8'h80: insn_has_modrm = 1'b1;
    8'hc5: insn_has_modrm = 1'b1;
    8'h00: insn_has_modrm = 1'b1;
    8'h3b: insn_has_modrm = 1'b1;
    8'hc0: insn_has_modrm = 1'b1;
    8'hde: insn_has_modrm = 1'b1;
    8'hd8: insn_has_modrm = 1'b1;
    8'h69: insn_has_modrm = 1'b1;
    8'h8c: insn_has_modrm = 1'b1;
    8'h2b: insn_has_modrm = 1'b1;
    8'h02: insn_has_modrm = 1'b1;
    8'hff: insn_has_modrm = 1'b1;
    8'h88: insn_has_modrm = 1'b1;
    8'hda: insn_has_modrm = 1'b1;
    8'h82: insn_has_modrm = 1'b1;
    8'hc4: insn_has_modrm = 1'b1;
    8'h38: insn_has_modrm = 1'b1;
    8'h8f: insn_has_modrm = 1'b1;
    8'hc1: insn_has_modrm = 1'b1;
    default: insn_has_modrm = 1'b0;
    endcase
endfunction

function logic [1:0] insn_immed_count;
    input logic [7:0] opcode;
    input logic [2:0] modrm_reg;

    unique casez ({opcode, modrm_reg})
    {8'h37, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hd5, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hd4, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h3f, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h10, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h11, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h12, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h13, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h14, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h15, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h80, 3'h2}: insn_immed_count = 2'd1;
    {8'h81, 3'h2}: insn_immed_count = 2'd1;
    {8'h82, 3'h2}: insn_immed_count = 2'd1;
    {8'h83, 3'h2}: insn_immed_count = 2'd1;
    {8'h00, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h01, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h02, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h03, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h04, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h05, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h80, 3'h0}: insn_immed_count = 2'd1;
    {8'h81, 3'h0}: insn_immed_count = 2'd1;
    {8'h82, 3'h0}: insn_immed_count = 2'd1;
    {8'h83, 3'h0}: insn_immed_count = 2'd1;
    {8'h20, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h21, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h22, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h23, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h24, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h25, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h80, 3'h4}: insn_immed_count = 2'd1;
    {8'h81, 3'h4}: insn_immed_count = 2'd1;
    {8'h82, 3'h4}: insn_immed_count = 2'd1;
    {8'h83, 3'h4}: insn_immed_count = 2'd1;
    {8'h62, 3'bzzz}: insn_immed_count = 2'd0;
    {8'he8, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h9a, 3'bzzz}: insn_immed_count = 2'd2;
    {8'hff, 3'h2}: insn_immed_count = 2'd0;
    {8'hff, 3'h3}: insn_immed_count = 2'd0;
    {8'h98, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hf8, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hfc, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hfa, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hf5, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h38, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h39, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h3a, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h3b, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h3c, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h3d, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h80, 3'h7}: insn_immed_count = 2'd1;
    {8'h81, 3'h7}: insn_immed_count = 2'd1;
    {8'h82, 3'h7}: insn_immed_count = 2'd1;
    {8'h83, 3'h7}: insn_immed_count = 2'd1;
    {8'ha6, 3'bzzz}: insn_immed_count = 2'd0;
    {8'ha7, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h99, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h27, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h2f, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hfe, 3'h1}: insn_immed_count = 2'd0;
    {8'hff, 3'h1}: insn_immed_count = 2'd0;
    {8'h48, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h49, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h4a, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h4b, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h4c, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h4d, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h4e, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h4f, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hf6, 3'h6}: insn_immed_count = 2'd0;
    {8'hf7, 3'h6}: insn_immed_count = 2'd0;
    {8'hc8, 3'bzzz}: insn_immed_count = 2'd2;
    {8'hd8, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hd9, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hda, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hdb, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hdc, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hdd, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hde, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hdf, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hf4, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hf6, 3'h7}: insn_immed_count = 2'd0;
    {8'hf7, 3'h7}: insn_immed_count = 2'd0;
    {8'hf6, 3'h5}: insn_immed_count = 2'd0;
    {8'hf7, 3'h5}: insn_immed_count = 2'd0;
    {8'h69, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h6b, 3'bzzz}: insn_immed_count = 2'd1;
    {8'he4, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hec, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hfe, 3'h0}: insn_immed_count = 2'd0;
    {8'hff, 3'h0}: insn_immed_count = 2'd0;
    {8'h40, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h41, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h42, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h43, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h44, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h45, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h46, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h47, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h6c, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h6d, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hcd, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hcc, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hce, 3'bzzz}: insn_immed_count = 2'd0;
    {8'he5, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hed, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hcf, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h72, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h76, 3'bzzz}: insn_immed_count = 2'd1;
    {8'he3, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h74, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h7c, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h7e, 3'bzzz}: insn_immed_count = 2'd1;
    {8'he9, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hea, 3'bzzz}: insn_immed_count = 2'd2;
    {8'heb, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hff, 3'h4}: insn_immed_count = 2'd0;
    {8'hff, 3'h5}: insn_immed_count = 2'd0;
    {8'h73, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h77, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h75, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h7d, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h7f, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h71, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h7b, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h79, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h70, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h7a, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h78, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h9f, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hc5, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h8d, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hc9, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hc4, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hac, 3'bzzz}: insn_immed_count = 2'd0;
    {8'had, 3'bzzz}: insn_immed_count = 2'd0;
    {8'he2, 3'bzzz}: insn_immed_count = 2'd1;
    {8'he1, 3'bzzz}: insn_immed_count = 2'd1;
    {8'he0, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h88, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h89, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h8a, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h8b, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hc6, 3'h0}: insn_immed_count = 2'd1;
    {8'hc7, 3'h0}: insn_immed_count = 2'd1;
    {8'hb0, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hb1, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hb2, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hb3, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hb4, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hb5, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hb6, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hb7, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hb8, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hb9, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hba, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hbb, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hbc, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hbd, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hbe, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hbf, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h8e, 3'h0}: insn_immed_count = 2'd0;
    {8'h8e, 3'h1}: insn_immed_count = 2'd0;
    {8'h8e, 3'h2}: insn_immed_count = 2'd0;
    {8'h8e, 3'h3}: insn_immed_count = 2'd0;
    {8'h8e, 3'h4}: insn_immed_count = 2'd0;
    {8'h8e, 3'h5}: insn_immed_count = 2'd0;
    {8'h8e, 3'h6}: insn_immed_count = 2'd0;
    {8'h8e, 3'h7}: insn_immed_count = 2'd0;
    {8'h8c, 3'h0}: insn_immed_count = 2'd0;
    {8'h8c, 3'h1}: insn_immed_count = 2'd0;
    {8'h8c, 3'h2}: insn_immed_count = 2'd0;
    {8'h8c, 3'h3}: insn_immed_count = 2'd0;
    {8'h8c, 3'h4}: insn_immed_count = 2'd0;
    {8'h8c, 3'h5}: insn_immed_count = 2'd0;
    {8'h8c, 3'h6}: insn_immed_count = 2'd0;
    {8'h8c, 3'h7}: insn_immed_count = 2'd0;
    {8'ha0, 3'bzzz}: insn_immed_count = 2'd1;
    {8'ha1, 3'bzzz}: insn_immed_count = 2'd1;
    {8'ha2, 3'bzzz}: insn_immed_count = 2'd1;
    {8'ha3, 3'bzzz}: insn_immed_count = 2'd1;
    {8'ha4, 3'bzzz}: insn_immed_count = 2'd0;
    {8'ha5, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hf6, 3'h4}: insn_immed_count = 2'd0;
    {8'hf7, 3'h4}: insn_immed_count = 2'd0;
    {8'hf6, 3'h3}: insn_immed_count = 2'd0;
    {8'hf7, 3'h3}: insn_immed_count = 2'd0;
    {8'h90, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hf6, 3'h2}: insn_immed_count = 2'd0;
    {8'hf7, 3'h2}: insn_immed_count = 2'd0;
    {8'h08, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h09, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h0a, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h0b, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h0c, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h0d, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h80, 3'h1}: insn_immed_count = 2'd1;
    {8'h81, 3'h1}: insn_immed_count = 2'd1;
    {8'h82, 3'h1}: insn_immed_count = 2'd1;
    {8'h83, 3'h1}: insn_immed_count = 2'd1;
    {8'he6, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hee, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h6e, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h6f, 3'bzzz}: insn_immed_count = 2'd0;
    {8'he7, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hef, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h58, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h59, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h5a, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h5b, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h5c, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h5d, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h5e, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h5f, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h07, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h17, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h1f, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h8f, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h61, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h9d, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hff, 3'h6}: insn_immed_count = 2'd0;
    {8'h06, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h0e, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h16, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h1e, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h50, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h51, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h52, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h53, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h54, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h55, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h56, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h57, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h68, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h6a, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h60, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h9c, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hd0, 3'h2}: insn_immed_count = 2'd0;
    {8'hd1, 3'h2}: insn_immed_count = 2'd0;
    {8'hc0, 3'h2}: insn_immed_count = 2'd1;
    {8'hc1, 3'h2}: insn_immed_count = 2'd1;
    {8'hd2, 3'h2}: insn_immed_count = 2'd0;
    {8'hd3, 3'h2}: insn_immed_count = 2'd0;
    {8'hd0, 3'h3}: insn_immed_count = 2'd0;
    {8'hd1, 3'h3}: insn_immed_count = 2'd0;
    {8'hc0, 3'h3}: insn_immed_count = 2'd1;
    {8'hc1, 3'h3}: insn_immed_count = 2'd1;
    {8'hd2, 3'h3}: insn_immed_count = 2'd0;
    {8'hd3, 3'h3}: insn_immed_count = 2'd0;
    {8'hc3, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hc2, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hcb, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hca, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hd0, 3'h0}: insn_immed_count = 2'd0;
    {8'hd1, 3'h0}: insn_immed_count = 2'd0;
    {8'hc0, 3'h0}: insn_immed_count = 2'd1;
    {8'hc1, 3'h0}: insn_immed_count = 2'd1;
    {8'hd2, 3'h0}: insn_immed_count = 2'd0;
    {8'hd3, 3'h0}: insn_immed_count = 2'd0;
    {8'hd0, 3'h1}: insn_immed_count = 2'd0;
    {8'hd1, 3'h1}: insn_immed_count = 2'd0;
    {8'hc0, 3'h1}: insn_immed_count = 2'd1;
    {8'hc1, 3'h1}: insn_immed_count = 2'd1;
    {8'hd2, 3'h1}: insn_immed_count = 2'd0;
    {8'hd3, 3'h1}: insn_immed_count = 2'd0;
    {8'h9e, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hd0, 3'h6}: insn_immed_count = 2'd0;
    {8'hd1, 3'h6}: insn_immed_count = 2'd0;
    {8'hc0, 3'h6}: insn_immed_count = 2'd1;
    {8'hc1, 3'h6}: insn_immed_count = 2'd1;
    {8'hd2, 3'h6}: insn_immed_count = 2'd0;
    {8'hd3, 3'h6}: insn_immed_count = 2'd0;
    {8'hd0, 3'h7}: insn_immed_count = 2'd0;
    {8'hd1, 3'h7}: insn_immed_count = 2'd0;
    {8'hc0, 3'h7}: insn_immed_count = 2'd1;
    {8'hc1, 3'h7}: insn_immed_count = 2'd1;
    {8'hd2, 3'h7}: insn_immed_count = 2'd0;
    {8'hd3, 3'h7}: insn_immed_count = 2'd0;
    {8'h18, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h19, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h1a, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h1b, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h1c, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h1d, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h80, 3'h3}: insn_immed_count = 2'd1;
    {8'h81, 3'h3}: insn_immed_count = 2'd1;
    {8'h82, 3'h3}: insn_immed_count = 2'd1;
    {8'h83, 3'h3}: insn_immed_count = 2'd1;
    {8'hae, 3'bzzz}: insn_immed_count = 2'd0;
    {8'haf, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hd6, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hd0, 3'h4}: insn_immed_count = 2'd0;
    {8'hd1, 3'h4}: insn_immed_count = 2'd0;
    {8'hc0, 3'h4}: insn_immed_count = 2'd1;
    {8'hc1, 3'h4}: insn_immed_count = 2'd1;
    {8'hd2, 3'h4}: insn_immed_count = 2'd0;
    {8'hd3, 3'h4}: insn_immed_count = 2'd0;
    {8'hd0, 3'h5}: insn_immed_count = 2'd0;
    {8'hd1, 3'h5}: insn_immed_count = 2'd0;
    {8'hc0, 3'h5}: insn_immed_count = 2'd1;
    {8'hc1, 3'h5}: insn_immed_count = 2'd1;
    {8'hd2, 3'h5}: insn_immed_count = 2'd0;
    {8'hd3, 3'h5}: insn_immed_count = 2'd0;
    {8'hf9, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hfd, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hfb, 3'bzzz}: insn_immed_count = 2'd0;
    {8'haa, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hab, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h28, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h29, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h2a, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h2b, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h2c, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h2d, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h80, 3'h5}: insn_immed_count = 2'd1;
    {8'h81, 3'h5}: insn_immed_count = 2'd1;
    {8'h82, 3'h5}: insn_immed_count = 2'd1;
    {8'h83, 3'h5}: insn_immed_count = 2'd1;
    {8'h84, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h85, 3'bzzz}: insn_immed_count = 2'd0;
    {8'ha8, 3'bzzz}: insn_immed_count = 2'd1;
    {8'ha9, 3'bzzz}: insn_immed_count = 2'd1;
    {8'hf6, 3'h0}: insn_immed_count = 2'd1;
    {8'hf6, 3'h1}: insn_immed_count = 2'd1;
    {8'hf7, 3'h0}: insn_immed_count = 2'd1;
    {8'hf7, 3'h1}: insn_immed_count = 2'd1;
    {8'h9b, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h86, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h87, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h91, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h92, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h93, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h94, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h95, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h96, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h97, 3'bzzz}: insn_immed_count = 2'd0;
    {8'hd7, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h30, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h31, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h32, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h33, 3'bzzz}: insn_immed_count = 2'd0;
    {8'h34, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h35, 3'bzzz}: insn_immed_count = 2'd1;
    {8'h80, 3'h6}: insn_immed_count = 2'd1;
    {8'h81, 3'h6}: insn_immed_count = 2'd1;
    {8'h82, 3'h6}: insn_immed_count = 2'd1;
    {8'h83, 3'h6}: insn_immed_count = 2'd1;
    default: insn_immed_count = 2'b0;
    endcase
endfunction

function logic insn_immed_is_8bit;
    input logic [7:0] opcode;
    input logic [2:0] modrm_reg;
    input logic immed_num;

    unique casez ({opcode, modrm_reg})
    {8'h37, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd5, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd4, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h3f, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h10, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h11, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h12, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h13, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h14, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h15, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h80, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h81, 3'h2}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h82, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h83, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h00, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h01, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h02, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h03, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h04, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h05, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h80, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h81, 3'h0}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h82, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h83, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h20, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h21, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h22, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h23, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h24, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h25, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h80, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h81, 3'h4}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h82, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h83, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h62, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'he8, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h9a, 3'bzzz}: insn_immed_is_8bit = ~|(2'h3 & (2'b1 << immed_num));
    {8'hff, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hff, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h98, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf8, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hfc, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hfa, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf5, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h38, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h39, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h3a, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h3b, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h3c, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h3d, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h80, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h81, 3'h7}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h82, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h83, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'ha6, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'ha7, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h99, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h27, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h2f, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hfe, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hff, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h48, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h49, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h4a, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h4b, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h4c, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h4d, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h4e, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h4f, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf6, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf7, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc8, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hd8, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd9, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hda, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hdb, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hdc, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hdd, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hde, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hdf, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf4, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf6, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf7, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf6, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf7, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h69, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h6b, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'he4, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hec, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hfe, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hff, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h40, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h41, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h42, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h43, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h44, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h45, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h46, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h47, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h6c, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h6d, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hcd, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hcc, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hce, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'he5, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hed, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hcf, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h72, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h76, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'he3, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h74, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h7c, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h7e, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'he9, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hea, 3'bzzz}: insn_immed_is_8bit = ~|(2'h3 & (2'b1 << immed_num));
    {8'heb, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hff, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hff, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h73, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h77, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h75, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h7d, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h7f, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h71, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h7b, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h79, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h70, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h7a, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h78, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h9f, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc5, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8d, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc9, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc4, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hac, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'had, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'he2, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'he1, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'he0, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h88, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h89, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8a, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8b, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc6, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc7, 3'h0}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hb0, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hb1, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hb2, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hb3, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hb4, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hb5, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hb6, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hb7, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hb8, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hb9, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hba, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hbb, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hbc, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hbd, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hbe, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hbf, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h8e, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8e, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8e, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8e, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8e, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8e, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8e, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8e, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8c, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8c, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8c, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8c, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8c, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8c, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8c, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8c, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'ha0, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'ha1, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'ha2, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'ha3, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'ha4, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'ha5, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf6, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf7, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf6, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf7, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h90, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf6, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf7, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h08, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h09, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h0a, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h0b, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h0c, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h0d, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h80, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h81, 3'h1}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h82, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h83, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'he6, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hee, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h6e, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h6f, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'he7, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hef, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h58, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h59, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h5a, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h5b, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h5c, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h5d, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h5e, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h5f, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h07, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h17, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h1f, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h8f, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h61, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h9d, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hff, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h06, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h0e, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h16, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h1e, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h50, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h51, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h52, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h53, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h54, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h55, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h56, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h57, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h68, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h6a, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h60, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h9c, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd0, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd1, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc0, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc1, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd2, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd3, 3'h2}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd0, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd1, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc0, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc1, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd2, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd3, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc3, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc2, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hcb, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hca, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hd0, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd1, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc0, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc1, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd2, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd3, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd0, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd1, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc0, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc1, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd2, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd3, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h9e, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd0, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd1, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc0, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc1, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd2, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd3, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd0, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd1, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc0, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc1, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd2, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd3, 3'h7}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h18, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h19, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h1a, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h1b, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h1c, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h1d, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h80, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h81, 3'h3}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h82, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h83, 3'h3}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hae, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'haf, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd6, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd0, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd1, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc0, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc1, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd2, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd3, 3'h4}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd0, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd1, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc0, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hc1, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd2, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd3, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf9, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hfd, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hfb, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'haa, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hab, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h28, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h29, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h2a, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h2b, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h2c, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h2d, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h80, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h81, 3'h5}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h82, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h83, 3'h5}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h84, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h85, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'ha8, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'ha9, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hf6, 3'h0}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf6, 3'h1}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hf7, 3'h0}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'hf7, 3'h1}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h9b, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h86, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h87, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h91, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h92, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h93, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h94, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h95, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h96, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h97, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'hd7, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h30, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h31, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h32, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h33, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h34, 3'bzzz}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h35, 3'bzzz}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h80, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h81, 3'h6}: insn_immed_is_8bit = ~|(2'h1 & (2'b1 << immed_num));
    {8'h82, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    {8'h83, 3'h6}: insn_immed_is_8bit = ~|(2'h0 & (2'b1 << immed_num));
    default: insn_immed_is_8bit = 1'b0;
    endcase
endfunction
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

// vi: ft=systemverilog
`ifndef MICROCODE_ROM_PATH
`define MICROCODE_ROM_PATH "."
`endif

`default_nettype none
module Microcode(input logic clk,
                 input logic reset,
                 input logic nmi_pulse,
                 input logic intr,
                 output logic inta,
                 output logic irq_to_mdr,
                 output logic start_interrupt,
                 output logic do_escape_fault,
                 output logic starting_instruction,
                 input logic stall,
                 input logic divide_error,
                 input logic rm_is_reg,
                 input logic [2:0] modrm_reg,
                 input logic int_enabled,
                 input logic zf,
                 input logic tf,
                 input logic fpu_busy,
                 output logic [15:0] microcode_immediate,
                 output logic [8:0] update_flags,
                 output logic modrm_start,
                 output logic use_microcode_immediate,
                 output logic [7:0] opcode,
                 input logic jump_taken,
                 input logic rb_zero,
                 output logic lock,
                 output logic multibit_shift,
                 output logic is_hlt,
                 output logic next_microinstruction,
                 // Microinstruction fields.
                 output logic [1:0] a_sel,
                 output logic [5:0] alu_op,
                 output logic [2:0] b_sel,
                 output logic ext_int_yield,
                 output logic io,
                 output logic load_ip,
                 output logic mar_wr_sel,
                 output logic mar_write,
                 output logic mdr_write,
                 output logic mem_read,
                 output logic mem_write,
                 output logic next_instruction,
                 output logic ra_modrm_rm_reg,
                 output logic [2:0] ra_sel,
                 output logic rb_cl,
                 output logic [2:0] rd_sel,
                 output logic [1:0] rd_sel_source,
                 output logic [1:0] reg_wr_source,
                 output logic [1:0] segment,
                 output logic segment_force,
                 output logic segment_wr_en,
                 output logic tmp_wr_en,
                 output logic tmp_wr_sel,
                 output logic width,
                 output logic reg_wr_en,
                 // Fifo Read Port.
                 output logic fifo_rd_en,
                 // verilator lint_off UNUSED
                 input Instruction next_instruction_value,
                 output Instruction cur_instruction,
                 // verilator lint_on UNUSED
                 input logic fifo_empty,
                 input logic fifo_resetting,
                 output logic loop_next,
                 input logic loop_done,
                 // Debug
                 output logic debug_stopped,
                 input logic debug_seize,
                 input logic [7:0] debug_addr,
                 input logic debug_run);

localparam num_instructions = 1198;
localparam addr_bits = 11;
localparam reset_address = 11'h129;
localparam nmi_address = 11'h12a;
localparam irq_address = 11'h12b;
localparam single_step_address = 11'h12c;
localparam divide_error_address = 11'h101;
localparam next_instruction_address = 11'h100;
localparam modrm_wait_address = 11'h12e;
localparam bad_opcode_address = 11'h12f;
localparam debug_wait_address = 11'h102;
localparam do_int_address = 11'h12d;

typedef struct packed {
    logic [10:0] next;
    logic [1:0] a_sel;
    logic [5:0] alu_op;
    logic [2:0] b_sel;
    logic ext_int_inhibit;
    logic ext_int_yield;
    logic [3:0] immediate;
    logic io;
    logic [3:0] jump_type;
    logic load_ip;
    logic mar_wr_sel;
    logic mar_write;
    logic mdr_write;
    logic mem_read;
    logic mem_write;
    logic next_instruction;
    logic ra_modrm_rm_reg;
    logic [2:0] ra_sel;
    logic rb_cl;
    logic [2:0] rd_sel;
    logic [1:0] rd_sel_source;
    logic [1:0] reg_wr_source;
    logic [1:0] segment;
    logic segment_force;
    logic segment_wr_en;
    logic tmp_wr_en;
    logic tmp_wr_sel;
    logic [3:0] update_flags;
    logic [1:0] width;
} microcode_instruction;

microcode_instruction mem[num_instructions] /* synthesis ram_init_file = "microcode.mif" */;
// verilator lint_off UNUSED
microcode_instruction current;
// verilator lint_on UNUSED
reg [addr_bits-1:0] addr;
reg [addr_bits-1:0] next_addr;
reg [addr_bits-1:0] jump_target;
assign use_microcode_immediate = |current.immediate;
assign opcode = cur_instruction.opcode;

always_comb begin
    case (current.immediate)
    1: microcode_immediate = 16'h0;
    2: microcode_immediate = 16'h18;
    3: microcode_immediate = 16'h2;
    4: microcode_immediate = 16'h14;
    5: microcode_immediate = 16'h1;
    6: microcode_immediate = 16'hffff;
    7: microcode_immediate = 16'hc;
    8: microcode_immediate = 16'hff;
    9: microcode_immediate = 16'h4;
    10: microcode_immediate = 16'h10;
    11: microcode_immediate = 16'h8;
    default: microcode_immediate = 16'h0;
    endcase
end

always_comb begin
    case (current.update_flags)
    0: update_flags = 9'h0;
    1: update_flags = 9'h5;
    2: update_flags = 9'h1a;
    3: update_flags = 9'h11f;
    4: update_flags = 9'h11b;
    5: update_flags = 9'h1;
    6: update_flags = 9'h1f;
    7: update_flags = 9'h40;
    8: update_flags = 9'h80;
    9: update_flags = 9'h11e;
    10: update_flags = 9'h60;
    11: update_flags = 9'h109;
    12: update_flags = 9'h1ff;
    13: update_flags = 9'h101;
    14: update_flags = 9'h1b;
    default: update_flags = 9'h0;
    endcase
end

assign a_sel = current.a_sel;
assign alu_op = current.alu_op;
assign b_sel = current.b_sel;
assign ext_int_yield = current.ext_int_yield;
assign io = current.io;
assign load_ip = current.load_ip;
assign mar_wr_sel = current.mar_wr_sel;
assign mar_write = current.mar_write;
assign mdr_write = current.mdr_write;
assign mem_read = current.mem_read;
assign mem_write = current.mem_write;
assign next_instruction = current.next_instruction;
assign ra_modrm_rm_reg = current.ra_modrm_rm_reg;
assign ra_sel = current.ra_sel;
assign rb_cl = current.rb_cl;
assign rd_sel = current.rd_sel;
assign rd_sel_source = current.rd_sel_source;
assign reg_wr_source = current.reg_wr_source;
assign segment = current.segment;
assign segment_force = current.segment_force;
assign segment_wr_en = current.segment_wr_en;
assign tmp_wr_en = current.tmp_wr_en;
assign tmp_wr_sel = current.tmp_wr_sel;

assign fifo_rd_en = starting_instruction;
assign starting_instruction = !stall && (next_addr == {{addr_bits-8{1'b0}}, next_instruction_value.opcode});
assign modrm_start = addr == modrm_wait_address ||
    (addr == next_instruction_address && !fifo_empty && next_instruction_value.has_modrm);
wire has_rep_prefix = cur_instruction.rep != REP_PREFIX_NONE;
reg rep_complete;
assign debug_stopped = addr == debug_wait_address;
assign multibit_shift = cur_instruction.opcode == 8'hd2 ||
                        cur_instruction.opcode == 8'hd3 ||
                        cur_instruction.opcode == 8'hc0 ||
                        cur_instruction.opcode == 8'hc1;
assign do_escape_fault = cur_instruction.opcode[7:3] == 5'b11011 && next_addr == do_int_address;
reg nmi_pending;
reg ext_int_inhibit;
wire take_nmi = (nmi_pending | nmi_pulse) & !ext_int_inhibit & !current.ext_int_inhibit;
wire take_irq = intr & int_enabled & !ext_int_inhibit & !current.ext_int_inhibit;
wire do_single_step = current.next_instruction & !ext_int_inhibit &
    trap_flag_set & current.next != debug_wait_address & !current.ext_int_inhibit;
assign start_interrupt = next_addr == nmi_address ||
                         next_addr == irq_address;
assign irq_to_mdr = next_addr == irq_address;
reg trap_flag_set;
assign is_hlt = cur_instruction.opcode == 8'hf4;
reg seized;
wire seizing = debug_seize & ~seized;
assign loop_next = !stall && current.jump_type == JumpType_LOOP_DONE;
assign reg_wr_en = current.rd_sel_source != RDSelSource_NONE & ~segment_wr_en;
assign next_microinstruction = addr != next_addr;
assign lock = cur_instruction.lock;

always_comb begin
    case (current.width)
    WidthType_W8: width = 1'b1;
    WidthType_W16: width = 1'b0;
    WidthType_WAUTO: width = ~cur_instruction.opcode[0];
    default: width = 1'b0;
    endcase
end

always_ff @(posedge clk)
    inta <= next_addr == irq_address && addr != irq_address;

always_ff @(posedge clk or posedge reset)
    if (reset)
        trap_flag_set <= 1'b0;
    else if (next_addr == single_step_address)
        trap_flag_set <= 1'b0;
    else if (starting_instruction)
        trap_flag_set <= tf;

always_ff @(posedge clk or posedge reset)
    if (reset)
        ext_int_inhibit <= 1'b0;
    else if (current.ext_int_inhibit && current.next != debug_wait_address)
        ext_int_inhibit <= 1'b1;
    else if (starting_instruction && !stall)
        ext_int_inhibit <= 1'b0;

`ifdef verilator
initial $readmemb({{`MICROCODE_ROM_PATH, "/microcode.bin"}}, mem);
`endif

always_comb begin
    case (cur_instruction.rep)
    REP_PREFIX_E: rep_complete = ~zf;
    REP_PREFIX_NE: rep_complete = zf;
    default: rep_complete = 1'b0;
    endcase
end

always_ff @(posedge clk or posedge reset)
    if (reset)
        nmi_pending <= 1'b0;
    else if (next_addr == nmi_address)
        nmi_pending <= 1'b0;
    else if (nmi_pulse)
        nmi_pending <= 1'b1;

always_ff @(posedge clk or posedge reset)
    if (reset)
        seized <= 1'b0;
    else if (debug_stopped)
        seized <= 1'b1;
    else if (!debug_seize)
        seized <= 1'b0;

always_comb begin
    unique case (current.jump_type)
    JumpType_RM_REG_MEM: jump_target = current.next + {{addr_bits-1{1'b0}}, ~rm_is_reg};
    JumpType_OPCODE: jump_target = !fifo_empty ? {{addr_bits-8{1'b0}}, next_instruction_value.opcode} : addr;
    JumpType_DISPATCH_REG: jump_target = current.next + {{addr_bits-3{1'b0}}, modrm_reg};
    JumpType_HAS_NO_REP_PREFIX: jump_target = ~has_rep_prefix ? current.next : addr + 1'b1;
    JumpType_ZERO: jump_target = zf ? current.next : addr + 1'b1;
    JumpType_REP_NOT_COMPLETE: jump_target = !rep_complete ? current.next : addr + 1'b1;
    JumpType_RB_ZERO: jump_target = rb_zero ? current.next : addr + 1'b1;
    JumpType_LOOP_DONE: jump_target = loop_done ? current.next : addr + 1'b1;
    JumpType_JUMP_TAKEN: jump_target = jump_taken ? current.next : addr + 1'b1;
    default: jump_target = current.next;
    endcase
end

always_comb begin
    if (reset)
        next_addr = reset_address;
    else if (debug_stopped && debug_run)
        next_addr = {{addr_bits - 9{1'b0}}, 1'b1, debug_addr};
    else if (stall)
        next_addr = addr;
    else if (current.ext_int_yield && seizing)
        next_addr = debug_wait_address;
    else if (current.ext_int_yield && take_nmi)
        next_addr = nmi_address;
    else if (current.ext_int_yield && take_irq)
        next_addr = irq_address;
    else if (addr == next_instruction_address && !fifo_empty && !fifo_resetting &&
             next_instruction_value.invalid)
        next_addr = bad_opcode_address;
    else if (current.jump_type != JumpType_UNCONDITIONAL)
        next_addr = jump_target;
    else if (divide_error)
        next_addr = divide_error_address;
    else if (current.next_instruction && take_nmi)
        next_addr = nmi_address;
    else if (current.next_instruction && take_irq)
        next_addr = irq_address;
    else if ((current.next_instruction && do_single_step) ||
             (is_hlt && trap_flag_set))
        next_addr = single_step_address;
    else if (current.next_instruction && debug_seize)
        next_addr = debug_wait_address;
    else if (current.next_instruction || (is_hlt && intr))
        next_addr = !fifo_empty && !fifo_resetting ?
            (next_instruction_value.has_modrm ? modrm_wait_address :
             {{addr_bits-8{1'b0}}, next_instruction_value.opcode}) :
            next_instruction_address;
    else
        next_addr = current.next;
end

always @(posedge clk)
    addr <= next_addr;

always @(posedge clk)
    current <= mem[next_addr];

always_ff @(posedge clk)
    if (fifo_rd_en)
        cur_instruction <= next_instruction_value;

`ifdef verilator
export "DPI-C" function get_microcode_address;

function bit [addr_bits-1:0] get_microcode_address;
    get_microcode_address = addr;
endfunction

export "DPI-C" function get_ext_int_yield;

function bit get_ext_int_yield;
    get_ext_int_yield = current.ext_int_yield;
endfunction

int microcode_coverage[num_instructions];

always_ff @(posedge clk)
    microcode_coverage[addr] <= microcode_coverage[addr] + 1;

export "DPI-C" function get_microcode_num_instructions;

function int get_microcode_num_instructions;
    get_microcode_num_instructions = num_instructions;
endfunction

export "DPI-C" function get_microcode_coverage_bin;

function int get_microcode_coverage_bin;
    input int bin;
    get_microcode_coverage_bin = microcode_coverage[bin];
endfunction
`endif

endmodule
