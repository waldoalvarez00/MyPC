//
// TV80 8-Bit Microprocessor Core
// Based on the VHDL T80 core by Daniel Wallner (jesus@opencores.org)
//
// Copyright (c) 2004 Guy Hutchison (ghutchis@opencores.org)
//
// Permission is hereby granted, free of charge, to any person obtaining a 
// copy of this software and associated documentation files (the "Software"), 
// to deal in the Software without restriction, including without limitation 
// the rights to use, copy, modify, merge, publish, distribute, sublicense, 
// and/or sell copies of the Software, and to permit persons to whom the 
// Software is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included 
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, 
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF 
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. 
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY 
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, 
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE 
// SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

module tv80_alu (/*AUTOARG*/
  // Outputs
  Q, F_Out, 
  // Inputs
  Arith16, Z16, ALU_Op, IR, ISet, BusA, BusB, F_In
  );

  parameter		Mode   = 0;
  parameter		Flag_C = 0;
  parameter		Flag_N = 1;
  parameter		Flag_P = 2;
  parameter		Flag_X = 3;
  parameter		Flag_H = 4;
  parameter		Flag_Y = 5;
  parameter		Flag_Z = 6;
  parameter		Flag_S = 7;

  input 		Arith16;
  input 		Z16;
  input [3:0]           ALU_Op ;
  input [5:0]           IR;
  input [1:0]           ISet;
  input [7:0]           BusA;
  input [7:0]           BusB;
  input [7:0]           F_In;
  output [7:0]          Q;
  output [7:0]          F_Out;
  reg [7:0]             Q;
  reg [7:0]             F_Out;

  function [4:0] AddSub4;
    input [3:0] A;
    input [3:0] B;
    input Sub;
    input Carry_In;
    begin
      AddSub4 = { 1'b0, A } + { 1'b0, (Sub)?~B:B } + {4'h0,Carry_In};
    end
  endfunction // AddSub4
  
  function [3:0] AddSub3;
    input [2:0] A;
    input [2:0] B;
    input Sub;
    input Carry_In;
    begin
      AddSub3 = { 1'b0, A } + { 1'b0, (Sub)?~B:B } + {3'h0,Carry_In};
    end
  endfunction // AddSub4

  function [1:0] AddSub1;
    input A;
    input B;
    input Sub;
    input Carry_In;
    begin
      AddSub1 = { 1'b0, A } + { 1'b0, (Sub)?~B:B } + {1'h0,Carry_In};
    end
  endfunction // AddSub4

  // AddSub variables (temporary signals)
  reg UseCarry;
  reg Carry7_v;
  reg OverFlow_v;
  reg HalfCarry_v;
  reg Carry_v;
  reg [7:0] Q_v;

  reg [7:0] BitMask;

  // Mode-aware carry flag read - GB uses F[4], Z80 uses F[0]
  wire carry_flag_in = (Mode == 3) ? F_In[4] : F_In[Flag_C];
  wire z_flag_in = (Mode == 3) ? F_In[7] : F_In[Flag_Z];
  wire s_flag_in = (Mode == 3) ? 1'b0 : F_In[Flag_S];
  wire p_flag_in = (Mode == 3) ? 1'b0 : F_In[Flag_P];

  always @(/*AUTOSENSE*/ALU_Op or BusA or BusB or F_In or IR)
    begin
      case (IR[5:3])
        3'b000 : BitMask = 8'b00000001;
        3'b001 : BitMask = 8'b00000010;
        3'b010 : BitMask = 8'b00000100;
        3'b011 : BitMask = 8'b00001000;
        3'b100 : BitMask = 8'b00010000;
        3'b101 : BitMask = 8'b00100000;
        3'b110 : BitMask = 8'b01000000;
        default: BitMask = 8'b10000000;
      endcase // case(IR[5:3])

      UseCarry = ~ ALU_Op[2] && ALU_Op[0];
      { HalfCarry_v, Q_v[3:0] } = AddSub4(BusA[3:0], BusB[3:0], ALU_Op[1], ALU_Op[1] ^ (UseCarry && carry_flag_in) );
      { Carry7_v, Q_v[6:4]  } = AddSub3(BusA[6:4], BusB[6:4], ALU_Op[1], HalfCarry_v);
      { Carry_v, Q_v[7] } = AddSub1(BusA[7], BusB[7], ALU_Op[1], Carry7_v);
      OverFlow_v = Carry_v ^ Carry7_v;
    end // always @ *
  
  reg [7:0] Q_t;
  reg [8:0] DAA_Q;
  reg       daa_n_in, daa_h_in, daa_c_in, daa_c_out;  // DAA helper regs

  always @ (/*AUTOSENSE*/ALU_Op or Arith16 or BitMask or BusA or BusB
	    or Carry_v or F_In or HalfCarry_v or IR or ISet
	    or OverFlow_v or Q_v or Z16)
    begin
      Q_t = 8'hxx;
      DAA_Q = {9{1'bx}};
      daa_n_in = 1'b0;
      daa_h_in = 1'b0;
      daa_c_in = 1'b0;
      daa_c_out = 1'b0;

      F_Out = F_In;
      case (ALU_Op)
	4'b0000, 4'b0001,  4'b0010, 4'b0011, 4'b0100, 4'b0101, 4'b0110, 4'b0111 :
          begin
	    F_Out[Flag_N] = 1'b0;
	    F_Out[Flag_C] = 1'b0;
            
	    case (ALU_Op[2:0])
              
	      3'b000, 3'b001 : // ADD, ADC
                begin
		  Q_t = Q_v;
		  F_Out[Flag_C] = Carry_v;
		  F_Out[Flag_H] = HalfCarry_v;
		  F_Out[Flag_P] = OverFlow_v;
                end
              
	      3'b010, 3'b011, 3'b111 : // SUB, SBC, CP
                begin
		  Q_t = Q_v;
		  F_Out[Flag_N] = 1'b1;
		  F_Out[Flag_C] = ~ Carry_v;
		  F_Out[Flag_H] = ~ HalfCarry_v;
		  F_Out[Flag_P] = OverFlow_v;
                end
              
	      3'b100 : // AND
                begin
		  Q_t[7:0] = BusA & BusB;
		  F_Out[Flag_H] = 1'b1;
                end
              
	      3'b101 : // XOR
                begin
		  Q_t[7:0] = BusA ^ BusB;
		  F_Out[Flag_H] = 1'b0;
                end
              
	      default : // OR 3'b110
                begin
		  Q_t[7:0] = BusA | BusB;
		  F_Out[Flag_H] = 1'b0;
                end
              
	    endcase // case(ALU_OP[2:0])
            
	    if (ALU_Op[2:0] == 3'b111 ) 
              begin // CP
		F_Out[Flag_X] = BusB[3];
		F_Out[Flag_Y] = BusB[5];
	      end 
            else 
              begin
		F_Out[Flag_X] = Q_t[3];
		F_Out[Flag_Y] = Q_t[5];
	      end
            
	    if (Q_t[7:0] == 8'b00000000 ) 
              begin
		F_Out[Flag_Z] = 1'b1;
		if (Z16 == 1'b1 ) 
                  begin
			    F_Out[Flag_Z] = z_flag_in;	// 16 bit ADC,SBC
			  end
		      end 
            else 
              begin
		F_Out[Flag_Z] = 1'b0;
	      end // else: !if(Q_t[7:0] == 8'b00000000 )
            
	    F_Out[Flag_S] = Q_t[7];
	    case (ALU_Op[2:0])
	      3'b000, 3'b001, 3'b010, 3'b011, 3'b111 : // ADD, ADC, SUB, SBC, CP
                ;
              
	      default :
	        F_Out[Flag_P] = ~(^Q_t);                    
	    endcase // case(ALU_Op[2:0])
            
		    if (Arith16 == 1'b1 ) 
		      begin
			F_Out[Flag_S] = s_flag_in;
			F_Out[Flag_Z] = z_flag_in;
			F_Out[Flag_P] = p_flag_in;
		      end
	          end // case: 4'b0000, 4'b0001,  4'b0010, 4'b0011, 4'b0100, 4'b0101, 4'b0110, 4'b0111
        
	4'b1100 :
          begin
	    // DAA - Decimal Adjust Accumulator
	    // GameBoy (Mode==3) uses different flag bit positions:
	    //   GB: Z=7, N=6, H=5, C=4, bits 3:0 always 0
	    //   Z80: S=7, Z=6, Y=5, H=4, X=3, P=2, N=1, C=0

	    // Read input flags at correct positions for the mode
	    daa_n_in = (Mode == 3) ? F_In[6] : F_In[Flag_N];
	    daa_h_in = (Mode == 3) ? F_In[5] : F_In[Flag_H];
	    daa_c_in = (Mode == 3) ? F_In[4] : F_In[Flag_C];

	    DAA_Q[7:0] = BusA;
	    DAA_Q[8] = 1'b0;
	    daa_c_out = daa_c_in;

	    if (Mode == 3) begin
	      // GameBoy DAA algorithm (SameBoy/bgb reference)
	      // Both conditions checked on ORIGINAL A value (BusA)
	      if (daa_n_in == 1'b0) begin
	        // After addition
	        // Both adjustments based on ORIGINAL value to determine if adjustment needed
	        if (daa_c_in || BusA > 8'h99) begin
	          DAA_Q = DAA_Q + 8'h60;
	          daa_c_out = 1'b1;
	        end
	        if (daa_h_in || (BusA[3:0] > 4'd9)) begin
	          DAA_Q = DAA_Q + 8'h06;
	        end
	      end else begin
	        // After subtraction
	        if (daa_c_in) begin
	          DAA_Q[7:0] = DAA_Q[7:0] - 8'h60;
	        end
	        if (daa_h_in) begin
	          DAA_Q[7:0] = DAA_Q[7:0] - 8'h06;
	        end
	      end
	    end else begin
	      // Z80 DAA algorithm
	      if (daa_n_in == 1'b0) begin
	        // After addition
	        if (DAA_Q[3:0] > 9 || daa_h_in) begin
	          DAA_Q = DAA_Q + 6;
	        end
	        if (DAA_Q[8:4] > 9 || daa_c_in) begin
	          DAA_Q = DAA_Q + 96;
	          daa_c_out = 1'b1;
	        end
	      end else begin
	        // After subtraction
	        if (DAA_Q[3:0] > 9 || daa_h_in) begin
	          DAA_Q[7:0] = DAA_Q[7:0] - 6;
	        end
	        if (BusA > 153 || daa_c_in) begin
	          DAA_Q[7:0] = DAA_Q[7:0] - 8'h60;
	        end
	      end
	    end

	    Q_t = DAA_Q[7:0];

	    // Write output flags in Z80 format - core will remap for GameBoy mode
	    // Z80 format: Flag_S=7, Flag_Z=6, Flag_Y=5, Flag_H=4, Flag_X=3, Flag_P=2, Flag_N=1, Flag_C=0
	    // The tv80_core remaps these to GameBoy format (Z=7, N=6, H=5, C=4) when Mode==3
	    if (Mode == 3) begin
	      // GameBoy DAA: output in Z80 format for core to remap
	      F_Out[Flag_Z] = (DAA_Q[7:0] == 8'b0) ? 1'b1 : 1'b0;  // Z
	      F_Out[Flag_N] = daa_n_in;                             // N preserved
	      F_Out[Flag_H] = 1'b0;                                 // H always cleared
	      F_Out[Flag_C] = daa_c_out;                            // C
	      // Unused bits in GameBoy mode but set them for consistency
	      F_Out[Flag_S] = DAA_Q[7];
	      F_Out[Flag_X] = DAA_Q[3];
	      F_Out[Flag_Y] = DAA_Q[5];
	      F_Out[Flag_P] = ~(^DAA_Q);
	    end else begin
	      // Z80 mode
	      F_Out[Flag_H] = daa_h_in;
	      F_Out[Flag_C] = daa_c_out;
	      F_Out[Flag_X] = DAA_Q[3];
	      F_Out[Flag_Y] = DAA_Q[5];
	      F_Out[Flag_Z] = (DAA_Q[7:0] == 8'b0) ? 1'b1 : 1'b0;
	      F_Out[Flag_S] = DAA_Q[7];
	      F_Out[Flag_P] = ~(^DAA_Q);
	    end
          end // case: 4'b1100
        
	4'b1101, 4'b1110 :
          begin
	    // RLD, RRD
	    Q_t[7:4] = BusA[7:4];
	    if (ALU_Op[0] == 1'b1 ) 
              begin
		Q_t[3:0] = BusB[7:4];
	      end 
            else 
              begin
		Q_t[3:0] = BusB[3:0];
	      end
	    F_Out[Flag_H] = 1'b0;
	    F_Out[Flag_N] = 1'b0;
	    F_Out[Flag_X] = Q_t[3];
	    F_Out[Flag_Y] = Q_t[5];
	    if (Q_t[7:0] == 8'b00000000 ) 
              begin
		F_Out[Flag_Z] = 1'b1;
	      end 
            else 
              begin
		F_Out[Flag_Z] = 1'b0;
	      end
	    F_Out[Flag_S] = Q_t[7];
            F_Out[Flag_P] = ~(^Q_t);
          end // case: when 4'b1101, 4'b1110
        
	4'b1001 :
          begin
	    // BIT
	    Q_t[7:0] = BusB & BitMask;
	    F_Out[Flag_S] = Q_t[7];
	    if (Q_t[7:0] == 8'b00000000 ) 
              begin
		F_Out[Flag_Z] = 1'b1;
		F_Out[Flag_P] = 1'b1;
	      end 
            else 
              begin
		F_Out[Flag_Z] = 1'b0;
		F_Out[Flag_P] = 1'b0;
	      end
	    F_Out[Flag_H] = 1'b1;
	    F_Out[Flag_N] = 1'b0;
	    F_Out[Flag_X] = 1'b0;
	    F_Out[Flag_Y] = 1'b0;
	    if (IR[2:0] != 3'b110 ) 
              begin
		F_Out[Flag_X] = BusB[3];
		F_Out[Flag_Y] = BusB[5];
	      end
          end // case: when 4'b1001
        
	4'b1010 :
	  // SET
	  Q_t[7:0] = BusB | BitMask;
        
	4'b1011 :
	  // RES
	  Q_t[7:0] = BusB & ~ BitMask;
        
	4'b1000 :
          begin
	    // ROT
	    case (IR[5:3])
	      3'b000 : // RLC
                begin
		  Q_t[7:1] = BusA[6:0];
		  Q_t[0] = BusA[7];
		  F_Out[Flag_C] = BusA[7];
                end
              
		      3'b010 : // RL
	                begin
			  Q_t[7:1] = BusA[6:0];
			  Q_t[0] = carry_flag_in;
			  F_Out[Flag_C] = BusA[7];
	                end
              
	      3'b001 : // RRC
                begin
		  Q_t[6:0] = BusA[7:1];
		  Q_t[7] = BusA[0];
		  F_Out[Flag_C] = BusA[0];
                end
              
		      3'b011 : // RR
	                begin                        
			  Q_t[6:0] = BusA[7:1];
			  Q_t[7] = carry_flag_in;
			  F_Out[Flag_C] = BusA[0];
	                end
              
	      3'b100 : // SLA
                begin
		  Q_t[7:1] = BusA[6:0];
		  Q_t[0] = 1'b0;
		  F_Out[Flag_C] = BusA[7];
                end
              
	      3'b110 : // SLL (Undocumented) / SWAP
                begin
		  if (Mode == 3 ) 
                    begin
		      Q_t[7:4] = BusA[3:0];
		      Q_t[3:0] = BusA[7:4];
		      F_Out[Flag_C] = 1'b0;                            
		    end 
                  else 
                    begin
		      Q_t[7:1] = BusA[6:0];
		      Q_t[0] = 1'b1;
		      F_Out[Flag_C] = BusA[7];
		    end // else: !if(Mode == 3 )
                end // case: 3'b110
              
	      3'b101 : // SRA
                begin
		  Q_t[6:0] = BusA[7:1];
		  Q_t[7] = BusA[7];
		  F_Out[Flag_C] = BusA[0];
                end
              
	      default : // SRL
                begin
		  Q_t[6:0] = BusA[7:1];
		  Q_t[7] = 1'b0;
		  F_Out[Flag_C] = BusA[0];
                end
	    endcase // case(IR[5:3])
            
	    F_Out[Flag_H] = 1'b0;
	    F_Out[Flag_N] = 1'b0;
	    F_Out[Flag_X] = Q_t[3];
	    F_Out[Flag_Y] = Q_t[5];
	    F_Out[Flag_S] = Q_t[7];
	    if (Q_t[7:0] == 8'b00000000 ) 
              begin
		F_Out[Flag_Z] = 1'b1;
	      end 
            else 
              begin
		F_Out[Flag_Z] = 1'b0;
	      end
            F_Out[Flag_P] = ~(^Q_t);

		    if (ISet == 2'b00 ) 
		      begin
			if (Mode == 3) begin
			  // GameBoy A-rotates (RLCA/RRCA/RLA/RRA) always clear Z.
			  F_Out[Flag_P] = 1'b0;
			  F_Out[Flag_S] = 1'b0;
			  F_Out[Flag_Z] = 1'b0;
			end else begin
			  F_Out[Flag_P] = F_In[Flag_P];
			  F_Out[Flag_S] = F_In[Flag_S];
			  F_Out[Flag_Z] = F_In[Flag_Z];
			end
		      end
	          end // case: 4'b1000
        
        
	default :
	  ;
        
      endcase // case(ALU_Op)
      
      Q = Q_t;
    end // always @ (Arith16, ALU_OP, F_In, BusA, BusB, IR, Q_v, Carry_v, HalfCarry_v, OverFlow_v, BitMask, ISet, Z16)
  
endmodule // T80_ALU
