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
                 output [15:0] mar_out,
                 output [15:0] mdr_out,  // can be sent to divider or ALU
                 input logic write_mdr,  // order from microcode unit
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
                 input io, // R/W to a port
					  
                 
					  input mem_read,  // microcode order
					  input mem_write, // microcode order
					  
                 input logic is_8bit, // 8 bit operation, otherwise 16 bits
                 input logic wr_en,   // same as mem_write
                 output logic busy    // causes stall in microcode unit
					  
					  
					  //input [1:0] wr_sel, maybe can be used to detect segment changes and do the address calculation
					  
					  
					  
					  );

					  
logic [5:0] current_state;
					  
// State Definitions (1 bit could be eliminated)

localparam [5:0]
  IDLE = 5'd0,
  UNALIGNED_FIRST_BYTE_READ_8Bit = 5'd1,
  READ = 5'd2,
  WRITE = 5'd3,
  UNALIGNED_FIRST_BYTE = 5'd4,
  UNALIGNED_SECOND_BYTE = 5'd5,
  COMPLETE = 5'd6,
  WAIT_ACK_READ = 5'd7,
  WAIT_ACK = 5'd8,
  WAIT_ACK_0 = 5'd9,
  UNALIGNED_FIRST_BYTE_WRITE  = 5'd10,
  WAIT_ACK_0_WRITE =  5'd11,
  UNALIGNED_SECOND_BYTE_WRITE =  5'd12,
  COMPLETE_0 =  5'd13,
  WAIT_ACK_WRITE = 5'd14,
  UNALIGNED_FIRST_BYTE_WRITE_8bit  = 5'd15;

 

logic [15:0] mar;
logic [15:0] mdr;

logic complete;

wire unaligned = mar[0];

assign busy = (mem_read | mem_write) & ~complete;



// TODO Optimize this FSM

  always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            current_state <= IDLE;
            complete <= 1'b0;
				
        end else begin
		  
            case (current_state)
				
                IDLE: begin
					 
					      if (write_mdr) mdr <= mdr_in;
						  
                    
							if (unaligned) begin
						  
						    if(is_8bit) begin
							 
							   // 8 bits unaligned
								
						      if (mem_read) begin
								    current_state <= UNALIGNED_FIRST_BYTE_READ_8Bit;
									 complete <= 1'b0;
									 
									 m_addr <= io ? {3'b0, mar[15:0]} : {segment, 3'b0} + {3'b0, mar[15:1]};
									 
							   end
								
					    	   if (mem_write) begin
								    complete <= 1'b0;
								    current_state <= UNALIGNED_FIRST_BYTE_WRITE_8bit;
									 
									 m_addr <= io ? {3'b0, mar[15:0]} : {segment, 3'b0} + {3'b0, mar_out[15:1]};
									 
								end
							
							
							 end else begin
							
							   // 16 bits unaligned
								
							   if(mem_write) begin
								 complete <= 1'b0;
								 m_addr <= io ? {3'b0, mar[15:1]} : {segment, 3'b0} + {3'b0, mar[15:1]};
						       current_state <= UNALIGNED_FIRST_BYTE_WRITE;
								 end
								 
						       if (mem_read) begin
							    complete <= 1'b0;
								 m_addr <= io ? {3'b0, mar[15:1]} : {segment, 3'b0} + {3'b0, mar[15:1]};
						       current_state <= UNALIGNED_FIRST_BYTE;
								 end
							
							 end
						  
						    
							  
						  end else begin
						  
						     // aligned
							  
						     if (mem_read) begin
							  complete <= 1'b0;
							  current_state <= READ;
							  m_addr <= io ? {3'b0, mar_out[15:0]} : {segment, 3'b0} + {3'b0, mar_out[15:1]};
							  end 
							  
							  if (mem_write) begin
							  complete <= 1'b0;
							  current_state <= WRITE;
							  m_addr <= io ? {3'b0, mar_out[15:0]} : {segment, 3'b0} + {3'b0, mar_out[15:1]};
							  end
							  
						  end
							
                end
					 
					 
                READ: begin
					 
                    m_access <= 1'b1;
                    m_wr_en <= 1'b0;
                    m_bytesel <= is_8bit ? 2'b01 : 2'b11;
						  
						  current_state <= WAIT_ACK_READ;
                    
						  
                end
					 
					 
					 UNALIGNED_FIRST_BYTE_READ_8Bit: begin
					 
                    m_wr_en <= 1'b0;
                    m_bytesel <= 2'b10;
						  m_access <= 1'b1;
						  
						  current_state <= WAIT_ACK;
						  
                end
					 
					 
					 
					 UNALIGNED_FIRST_BYTE: begin
					 
                    m_wr_en <= 1'b0;
                    m_bytesel <= 2'b10;
						  m_access <= 1'b1;
						  
						  current_state <= WAIT_ACK_0;
						  
                end
					 
					 UNALIGNED_FIRST_BYTE_WRITE_8bit: begin
					 
                    m_wr_en <= 1'b1;
						  m_access <= 1'b1;
						  
                    m_bytesel <= 2'b10;
						  
						  m_data_out <= {mdr[7:0], 8'b0}; // Unaligned and first byte
						  current_state <= WAIT_ACK_WRITE;
						  
                end
					 
					 
					 UNALIGNED_FIRST_BYTE_WRITE: begin
					 
                    m_wr_en <= 1'b1;
						  m_access <= 1'b1;
						  
                    m_bytesel <= 2'b10;
						  
						  m_data_out <= {mdr[7:0], 8'b0}; // Unaligned and first byte
						  current_state <= WAIT_ACK_0_WRITE;
						  
                end
					 
					 
					 WAIT_ACK_0_WRITE: begin
					 
					   if (m_ack) begin
						    current_state <= UNALIGNED_SECOND_BYTE_WRITE;
							 m_addr <= m_addr + 1'b1;
							 m_access <= 1'b0;
							 m_wr_en <= 1'b0;
						  end
					 end
					 
					 
					 
                UNALIGNED_SECOND_BYTE_WRITE: begin
					 
                    m_access <= 1'b1;
                    m_wr_en <= 1'b1;
                    m_bytesel <= 2'b01;
						  m_data_out <= {8'b0, mdr[15:8]}; // Unaligned and second byte
						  current_state <= WAIT_ACK_WRITE;
                    
                end
					 
					 
					 
					 WAIT_ACK_WRITE: begin
					 
					   if (m_ack) begin
						    current_state <= COMPLETE;
							 complete <= 1'b1;
							 m_access <= 1'b0;
							 m_wr_en <= 1'b0;
							 m_addr <= 19'd0; // Stops noise on the BUS
						    m_data_out <= 16'd0;
						  end
					 end
					 
					 

					 
                WRITE: begin
                    m_access <= 1'b1;
                    m_wr_en <= 1'b1;
                    m_bytesel <= is_8bit ? 2'b01 : 2'b11;
						  m_data_out <= mdr;
						  current_state <= WAIT_ACK;
                end


					 
                UNALIGNED_FIRST_BYTE: begin
					 
					     m_access <= 1'b1;
                    m_wr_en <= 1'b0;
                    m_bytesel <= 2'b10;
						  m_access <= 1'b1;
						  
						  current_state <= WAIT_ACK_0;
						  
                end
					 
					 
					 
					 WAIT_ACK_0: begin
					 
					   if (m_ack) begin
						    current_state <= UNALIGNED_SECOND_BYTE;
							 
							 m_addr <= m_addr + 1'b1;
							 m_access <= 1'b0;
							 m_wr_en <= 1'b0;
						  end
					 end
					 
					 
                UNALIGNED_SECOND_BYTE: begin
					 
                    m_access <= 1'b1;
                    m_wr_en  <= 1'b1;
                    m_bytesel <= 2'b01;
						  current_state <= WAIT_ACK;
                    
                end
					 
					 
					 
					 WAIT_ACK: begin
					 
					   if (m_ack) begin
						    current_state <= COMPLETE;
							 complete <= 1'b1;
							 m_access <= 1'b0;
							 m_wr_en  <= 1'b0;
							 
							 // Stops noise on the BUS
							 m_addr <= 19'd0; 
						    m_data_out <= 16'd0;
						  end
					 end
					 
					 
					
					 
					 WAIT_ACK_READ: begin
					 
					   if (m_ack) begin
						    mdr <= is_8bit ? {8'b0, m_data_in[7:0]} : m_data_in;
						    current_state <= COMPLETE;
							 complete <= 1'b1;
							 
							 m_access <= 1'b0;
							 m_wr_en  <= 1'b0;
							 
							 // Stops noise on the BUS
							 m_addr <= 19'd0; 
						  
					   end
					 
				    end
					 
					 
                COMPLETE: begin
                    //complete <= 1'b0; // triggers busy for 1 clk (small glitch)
						  m_access <= 1'b0;
						  m_wr_en  <= 1'b0;
                    current_state <= COMPLETE_0;
						  
						  m_addr <= 19'd0;
						  m_data_out <= 16'd0;
                end
					 
					 
					 COMPLETE_0: begin
					     // To remove this wait state we need to change microcode unit
                    complete <= 1'b0;
                    current_state <= IDLE;
                end
					 
					 
					 
            endcase
        end
    end

	 
	 
	 
	 
	 
    //always_comb begin
	 
	     // this takes so long that is taking more that a single clock and creating spurious address on the bus 
	 
        //m_addr = io ? {3'b0, mar[15:1]} + {18'b0, second_byte} : {segment, 3'b0} + {3'b0, mar[15:1]} + {18'b0, second_byte};
		  
    //end
	 
	 
	 
	 

	 
	 always_ff @(posedge clk or posedge reset)
    if (reset)
        mar <= 16'b0;
    else if(write_mar)
        mar <= mar_in;
	 

    
    assign mar_out = mar;
    assign mdr_out = mdr;
	 
	 
	 
endmodule

				  

				  
				  
				  

