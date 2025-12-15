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
module LoadStore(input clk,
                 input reset,
					  
                 // Memory Address Register
                 input logic write_mar,      // microcode order
                 input logic [15:0] segment, // 80x86 segment register value comming from Segment Register File
                 input [15:0] mar_in,
					  
                 // Memory Data Register
                 output wire [15:0] mar_out,
                 output wire [15:0] mdr_out,  // can be sent to divider or ALU
                 input logic write_mdr,       // order from microcode unit
                 input [15:0] mdr_in,
					  
                 // Memory bus
                 output logic [19:1] m_addr,
                 input logic [15:0] m_data_in,
                 output logic [15:0] m_data_out,
                 output logic m_access,
					  
                 input logic m_ack,  // Acknowledge from other unit write performed or read data available
					  
                 output logic m_wr_en,
                 output logic [1:0] m_bytesel, // Mask for byte to access R/W (0 the byte is ignored)
					  
					  
					  
					  
					  
                 // Control
                 input  io, // R/W to a port
					  
                 
					  input  wire mem_read,  // microcode order
					  input  wire mem_write, // microcode order
					  
                 input  logic is_8bit,  // 8 bit operation, otherwise 16 bits
                 input  logic wr_en,    // same as mem_write
                 output logic busy      // causes stall in microcode unit
					  
					  
					  //input [1:0] wr_sel, maybe can be used to detect segment changes and do the address calculation
					  
					  
					  
					  );

					  
logic [5:0] current_state;
					  
// State Definitions

localparam [5:0]
  IDLE = 5'd0,
  READ_ALIGNED_UNALIGNED_8BIT_START = 5'd1,
  // READ_ALIGNED = 5'd2,           // Removed - deprecated (Phase 2 optimization)
  // WRITE_ALIGNED = 5'd3,          // Removed - deprecated (Phase 2 optimization)
  UNALIGNED_FIRST_BYTE = 5'd4,
  UNALIGNED_SECOND_BYTE = 5'd5,
  // READ_WRITE_COMPLETE = 5'd6,    // Removed - deprecated (Phase 2 optimization)
  WAIT_ACK_READ_ALIGNED = 5'd7,
  WAIT_UNALIGNED_READ_ACK_END = 5'd8,
  WAIT_UNALIGNED_READ_ACK_START = 5'd9,
  UNALIGNED_FIRST_BYTE_WRITE_ALIGNED  = 5'd10,
  WAIT_UNALIGNED_WRITE_ACK_START =  5'd11,
  UNALIGNED_SECOND_BYTE_WRITE_ALIGNED =  5'd12,
  // FINALIZE_OPERATION removed - Phase 1 optimization
  WAIT_ACK_WRITE_ALIGNED = 5'd14,
  UNALIGNED_FIRST_BYTE_WRITE_ALIGNED_8bit  = 5'd15,

  IO_READ_ALIGNED = 5'd16,
  IO_WRITE_ALIGNED = 5'd17,

  WAIT_UNALIGNED_8BIT_READ_ACK = 5'd18,
  WAIT_ACK_WRITE_ALIGNED16 = 5'd19,
  IO_WAIT_ACK_READ_ALIGNED = 5'd20;

 

logic [15:0] mar;
logic [15:0] mdr;

logic complete;

wire unaligned = mar[0];

assign busy = (mem_read | mem_write) & ~complete;

// Phase 1 Optimization: Pre-calculated physical address
// Computed when MAR is written to avoid critical path in memory access
logic [19:1] physical_addr;

// Optimized FSM - Phase 1 improvements:
// - Removed FINALIZE_OPERATION state (1 cycle saved on all operations)
// - Pre-calculated segment+offset address (timing improvement)
//
// Phase 2 improvements:
// - Eliminated READ_ALIGNED/WRITE_ALIGNED states (control signals set in IDLE)
// - Eliminated READ_WRITE_COMPLETE transition (WAIT_ACK states go directly to IDLE)
// - Result: Aligned operations reduced from 4 cycles to 2 cycles (50% improvement)
// - Result: All operations benefit from 2-cycle reduction in completion path

  always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            current_state <= IDLE;
            complete <= 1'b0;
            mdr <= 16'h0000;

        end else begin
		  
		      if (write_mdr) mdr <= mdr_in;
		  
            case (current_state)
				
                IDLE: begin

					         // Phase 2 Debug: Log IDLE state entry
					         if (mem_read || mem_write) begin
					             $display("[LoadStore DEBUG] IDLE: mem_read=%b mem_write=%b io=%b unaligned=%b is_8bit=%b",
					                      mem_read, mem_write, io, unaligned, is_8bit);
					             $display("[LoadStore DEBUG]       mdr=0x%04x physical_addr=0x%05x", mdr, physical_addr);
					         end

							if(io) begin
							
							  // IO is simple, no need to pack bytes into words
							  
							  m_addr <= {3'b0, mar[15:0]};
							  
							  
							  if (mem_read) begin
							    current_state <= IO_READ_ALIGNED;
							  end
							  
							  
							  if (mem_write) begin
							    current_state <= IO_WRITE_ALIGNED;
							  end
							  
							  
							end // IO End
							else begin
							
							   // Memory are packed bytes into words
								
								
								if (unaligned) begin
						  
						         if(is_8bit) begin
							 
							       // 8 bits unaligned
								
						          if (mem_read) begin
								       current_state <= READ_ALIGNED_UNALIGNED_8BIT_START;
									    complete <= 1'b0;
									    m_addr <= physical_addr;  // Phase 1: Use pre-calculated address

							       end

					    	       if (mem_write) begin
								        complete <= 1'b0;
								        current_state <= UNALIGNED_FIRST_BYTE_WRITE_ALIGNED_8bit;
									     m_addr <= physical_addr;  // Phase 1: Use pre-calculated address
								    end
							
							
							     end else begin
							
							      // 16 bits unaligned

							      if(mem_write) begin
								     complete <= 1'b0;
								     m_addr <= physical_addr;  // Phase 1: Use pre-calculated address
						           current_state <= UNALIGNED_FIRST_BYTE_WRITE_ALIGNED;
								   end

						         if (mem_read) begin
							        complete <= 1'b0;
								     m_addr <= physical_addr;  // Phase 1: Use pre-calculated address
						           current_state <= UNALIGNED_FIRST_BYTE;
								   end
							
							 end
						  
						    
							  
						  end else begin

						     // aligned - Phase 2: Set control signals directly in IDLE

						     if (mem_read) begin
						         $display("[LoadStore DEBUG] IDLE->WAIT_ACK_READ: Setting m_access=1, m_wr_en=0, bytesel=%b",
						                  is_8bit ? 2'b01 : 2'b11);
							    complete <= 1'b0;
							    m_addr <= physical_addr;  // Phase 1: Use pre-calculated address
							    // Phase 2: Set control signals immediately, skip READ_ALIGNED state
							    m_access <= 1'b1;
							    m_wr_en <= 1'b0;
							    m_bytesel <= is_8bit ? 2'b01 : 2'b11;
							    current_state <= WAIT_ACK_READ_ALIGNED;
							  end else if (mem_write) begin
						         $display("[LoadStore DEBUG] IDLE->WAIT_ACK_WRITE: Setting m_access=1, m_wr_en=1, mdr=0x%04x", mdr);
							    complete <= 1'b0;
							    m_addr <= physical_addr;  // Phase 1: Use pre-calculated address
							    // Phase 2: Set control signals immediately, skip WRITE_ALIGNED state
							    m_access <= 1'b1;
							    m_wr_en <= 1'b1;
							    m_bytesel <= is_8bit ? 2'b01 : 2'b11;
							    m_data_out <= mdr;
							    current_state <= WAIT_ACK_WRITE_ALIGNED16;
							  end

						  end
								
							
							end
							
							
                    
							
							
                end // IDLE END
					 
					 
					 
					 IO_READ_ALIGNED: begin
					 
					     m_access <= 1'b1;
                    m_wr_en <= 1'b0;
                    m_bytesel <= is_8bit ? 2'b01 : 2'b11;
						  current_state <= IO_WAIT_ACK_READ_ALIGNED;
					 end
					 
					 IO_WAIT_ACK_READ_ALIGNED: begin

					   if (m_ack) begin
						    mdr <= is_8bit ? {8'b0, m_data_in[7:0]} : m_data_in;
						    // Phase 2: Go directly to IDLE
						    current_state <= IDLE;
							 complete <= 1'b1;

							 m_access <= 1'b0;
							 m_wr_en  <= 1'b0;

							 // Stops noise on the BUS
							 m_addr <= 19'd0;
						  end else begin
						    // Phase 2: Clear complete when waiting
						    complete <= 1'b0;
					   end

				    end


					 READ_ALIGNED_UNALIGNED_8BIT_START: begin
					 
                    m_wr_en <= 1'b0;
                    m_bytesel <= 2'b10;
						  m_access <= 1'b1;
						  
						  current_state <= WAIT_UNALIGNED_8BIT_READ_ACK;
						  
                end
					 
					 
					 WAIT_UNALIGNED_8BIT_READ_ACK: begin

					   if (m_ack) begin
						    // Phase 2: Go directly to IDLE
						    current_state <= IDLE;
							 complete <= 1'b1;
							 m_access <= 1'b0;
							 m_wr_en  <= 1'b0;

							 mdr[7:0] <= m_data_in[15:8];
							 // Stops noise on the BUS
							 m_addr <= 19'd0;
						    m_data_out <= 16'd0;
						  end else begin
						    // Phase 2: Clear complete when waiting
						    complete <= 1'b0;
						  end
					 end
					 
					 
					 UNALIGNED_FIRST_BYTE: begin
					 
                    m_wr_en <= 1'b0;
                    m_bytesel <= 2'b10;
						  m_access <= 1'b1;
						  
						  current_state <= WAIT_UNALIGNED_READ_ACK_START;
						  
                end
					 
					 UNALIGNED_FIRST_BYTE_WRITE_ALIGNED_8bit: begin
					 
                    m_wr_en <= 1'b1;
						  m_access <= 1'b1;
						  
                    m_bytesel <= 2'b10;
						  
						  m_data_out <= {mdr[7:0], 8'b0}; // Unaligned and first byte
						  current_state <= WAIT_ACK_WRITE_ALIGNED;
						  
                end
					 
					 
					 UNALIGNED_FIRST_BYTE_WRITE_ALIGNED: begin
					 
                    m_wr_en <= 1'b1;
						  m_access <= 1'b1;
						  
                    m_bytesel <= 2'b10;
						  
						  m_data_out <= {mdr[7:0], 8'b0}; // Unaligned and first byte
						  current_state <= WAIT_UNALIGNED_WRITE_ACK_START;
						  
                end
					 
					 
					 WAIT_UNALIGNED_WRITE_ACK_START: begin
					 
					   if (m_ack) begin
						    current_state <= UNALIGNED_SECOND_BYTE_WRITE_ALIGNED;
							 m_addr <= m_addr + 1'b1;
							 m_access <= 1'b0;
							 m_wr_en <= 1'b0;
						  end
					 end
					 
					 
					 
                UNALIGNED_SECOND_BYTE_WRITE_ALIGNED: begin
					 
                    m_access <= 1'b1;
                    m_wr_en <= 1'b1;
                    m_bytesel <= 2'b01;
						  m_data_out <= {8'b0, mdr[15:8]}; // Unaligned and second byte
						  current_state <= WAIT_ACK_WRITE_ALIGNED;
                    
                end
					 
					 
					 
					 WAIT_ACK_WRITE_ALIGNED: begin

					   if (m_ack) begin
						    // Phase 2: Go directly to IDLE
						    current_state <= IDLE;
							 complete <= 1'b1;
							 m_access <= 1'b0;
							 m_wr_en <= 1'b0;
							 m_addr <= 19'd0; // Stops noise on the BUS
						    m_data_out <= 16'd0;
						  end else begin
						    // Phase 2: Clear complete when waiting
						    complete <= 1'b0;
						  end
					 end
					 
					 
					 
					 IO_WRITE_ALIGNED: begin
                    m_access <= 1'b1;
                    m_wr_en <= 1'b1;
                    m_bytesel <= is_8bit ? 2'b01 : 2'b11;
						  m_data_out <= mdr;
						  current_state <= WAIT_ACK_WRITE_ALIGNED16;
                end


					 WAIT_ACK_WRITE_ALIGNED16: begin
					   $display("[LoadStore DEBUG] WAIT_ACK_WRITE: m_ack=%b m_access=%b m_wr_en=%b", m_ack, m_access, m_wr_en);

					   if (m_ack) begin
					       $display("[LoadStore DEBUG] WAIT_ACK_WRITE: ACK received, transitioning to IDLE, complete=1");
						    // Phase 2: Go directly to IDLE, eliminating READ_WRITE_COMPLETE
						    current_state <= IDLE;
							 complete <= 1'b1;
							 m_access <= 1'b0;
							 m_wr_en  <= 1'b0;

							 // Stops noise on the BUS
							 m_addr <= 19'd0;
						    m_data_out <= 16'd0;
						  end else begin
						    // Phase 2: Clear complete when waiting
						    complete <= 1'b0;
						  end
					 end

					 

					 
                UNALIGNED_FIRST_BYTE: begin
					 
					     m_access <= 1'b1;
                    m_wr_en <= 1'b0;
                    m_bytesel <= 2'b10;
						  m_access <= 1'b1;
						  
						  current_state <= WAIT_UNALIGNED_READ_ACK_START;
						  
                end
					 
					 
					 
					 WAIT_UNALIGNED_READ_ACK_START: begin
					 
					   if (m_ack) begin
						    current_state <= UNALIGNED_SECOND_BYTE;
							 mdr[7:0] <= m_data_in[15:8];
							 m_addr <= m_addr + 1'b1;
							 m_access <= 1'b0;
							 m_wr_en <= 1'b0;
						  end
					 end
					 
					 
                UNALIGNED_SECOND_BYTE: begin
					 
                    m_access <= 1'b1;
                    m_wr_en  <= 1'b0;
                    m_bytesel <= 2'b01;
						  current_state <= WAIT_UNALIGNED_READ_ACK_END;
                    
                end
					 
					 
					 
					 WAIT_UNALIGNED_READ_ACK_END: begin

					   if (m_ack) begin
						    // Phase 2: Go directly to IDLE
						    current_state <= IDLE;
							 complete <= 1'b1;
							 m_access <= 1'b0;
							 m_wr_en  <= 1'b0;

							 mdr[15:8] <= m_data_in[7:0];
							 // Stops noise on the BUS
							 m_addr <= 19'd0;
						    m_data_out <= 16'd0;
						  end else begin
						    // Phase 2: Clear complete when waiting
						    complete <= 1'b0;
						  end
					 end
					 
					 
					
					 
					 WAIT_ACK_READ_ALIGNED: begin
					   $display("[LoadStore DEBUG] WAIT_ACK_READ: m_ack=%b m_data_in=0x%04x", m_ack, m_data_in);

					   if (m_ack) begin
					       $display("[LoadStore DEBUG] WAIT_ACK_READ: ACK received, transitioning to IDLE, complete=1");
						    mdr <= is_8bit ? {8'b0, m_data_in[7:0]} : m_data_in;
						    // Phase 2: Go directly to IDLE, eliminating READ_WRITE_COMPLETE
						    current_state <= IDLE;
							 complete <= 1'b1;

							 m_access <= 1'b0;
							 m_wr_en  <= 1'b0;

							 // Stops noise on the BUS
							 m_addr <= 19'd0;
						  end else begin
						    // Phase 2: Clear complete when waiting
						    complete <= 1'b0;
					   end

				    end


            endcase
        end
    end

	 
	 
	 

	 
	 


	 // Phase 1 Optimization: Pre-calculate physical address when MAR is written
	 // This removes the 19-bit addition from the critical path during memory access
	 always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            mar <= 16'b0;
            physical_addr <= 19'b0;
        end else if(write_mar) begin
            mar <= mar_in;
            // Pre-calculate: physical_addr = (segment << 4) + (mar >> 1)
            // Segment shift by 4 bits (multiply by 16) + word-aligned MAR
            physical_addr <= {segment, 3'b0} + {3'b0, mar_in[15:1]};
        end
    end



    assign mar_out = mar;
    assign mdr_out = mdr;
	 
	 
	 
endmodule

				  

				  
				  
				  

