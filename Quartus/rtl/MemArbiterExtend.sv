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



// The primary purpose of this module is to ensure that when both buses request 
// access to the shared memory, only one of them is granted access at a time

module MemArbiterExtend(

    input  clk,
    input  reset,
    
    // CPU bus
    input  [19:1] cpu_m_addr,
    output logic [15:0] cpu_m_data_in,
    input  [15:0] cpu_m_data_out,
    input  cpu_m_access,
    output  cpu_m_ack,
    input  cpu_m_wr_en,
    input  [1:0] cpu_m_bytesel,

    // MCGA bus
    input  [19:1] mcga_m_addr,
    output logic [15:0] mcga_m_data_in,
    input  [15:0] mcga_m_data_out,
    input  mcga_m_access,
    output  mcga_m_ack,
    input  mcga_m_wr_en,
    input  [1:0] mcga_m_bytesel,

    // Output bus
    output logic [19:1] sdram_m_addr,
    input  [15:0] sdram_m_data_in,
    output logic [15:0] sdram_m_data_out,
    output logic sdram_m_access,
    input  sdram_m_ack,
    output logic sdram_m_wr_en,
    output logic [1:0] sdram_m_bytesel,
    output  q_b
	 
	 // Debug FSM
	 //output  [2:0] current_state
);


    logic grant_active;
	 logic last_served_A;
	 logic servingA;
    logic [2:0] arb_state;
	 //logic [2:0] current_state;
	 
    
    // Extended state machine with explicit wait for ack to be raised
    // proper round-robin scheduling
	 
    localparam [2:0] IDLE = 3'b000, SERVING_A = 3'b001, WAIT_A = 3'b010, 
                     SERVING_B = 3'b011, WAIT_B = 3'b100;

    

    initial begin
        arb_state = IDLE;
        last_served_A = 1'b0;
		  servingA= 1'b1;
    end

    always_ff @(posedge clk or posedge reset) begin
	 
	 
        if (reset) begin
            arb_state <= IDLE;
            last_served_A <= 1'b0;
				servingA <= 1'b1;
        end else begin
		  
		      //current_state <= arb_state; // Assign the state to output
				
            case (arb_state)
				
				
                IDLE: begin
                    if(last_served_A) begin
						    // Give priority to B
						    if(mcga_m_access) begin
							   arb_state <= SERVING_B;
								servingA <= 1'b0;
								grant_active <= 1'b1;
								
							 end
							 else begin
							   if (cpu_m_access) begin
								  arb_state <= SERVING_A;
								  servingA <= 1'b1;
								  grant_active <= 1'b1;
								  
								end
							 end
						  end
						  else begin
						     // Give priority to A
						     if(cpu_m_access) begin
							   arb_state <= SERVING_A;
								servingA <= 1'b1;
								grant_active <= 1'b1;
								
							 end
							 else begin
							   if (mcga_m_access) begin
								  arb_state <= SERVING_B;
								  servingA <= 1'b0;
								  grant_active <= 1'b1;
								  
								end
							 end
						  
						  end
                end
					 
					 
                SERVING_A: begin
					 
					     
					     
                    if (sdram_m_ack) begin
						      last_served_A <= 1'b1;
                        //arb_state <= WAIT_A;
								arb_state <= IDLE;
								grant_active <= 1'b0;
                    end 
						  else grant_active <= 1'b1;
						  
                end
					 
					 
					 
                SERVING_B: begin
					 
					     
					     
                    if (sdram_m_ack) begin
						      last_served_A <= 1'b0;
                        //arb_state <= WAIT_B;
								
								arb_state <= IDLE;
								grant_active <= 1'b0;
                    end
						  else grant_active <= 1'b1;
                end
					 
					 
					 
					 
                default: arb_state <= IDLE;
            endcase
        end
    end

// Register ACK and data outputs to prevent glitches and ensure timing
logic cpu_m_ack_reg;
logic mcga_m_ack_reg;
logic [15:0] cpu_m_data_in_reg;
logic [15:0] mcga_m_data_in_reg;

assign cpu_m_ack  = cpu_m_ack_reg;
assign mcga_m_ack = mcga_m_ack_reg;
assign cpu_m_data_in  = cpu_m_data_in_reg;
assign mcga_m_data_in = mcga_m_data_in_reg;

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        cpu_m_ack_reg  <= 1'b0;
        mcga_m_ack_reg <= 1'b0;
        cpu_m_data_in_reg  <= 16'b0;
        mcga_m_data_in_reg <= 16'b0;
    end else begin
        cpu_m_ack_reg  <= grant_active &  servingA & sdram_m_ack;
        mcga_m_ack_reg <= grant_active & ~servingA & sdram_m_ack;

        // Capture data when SDRAM ACK is high
        if (sdram_m_ack) begin
            if (servingA)
                cpu_m_data_in_reg <= sdram_m_data_in;
            else
                mcga_m_data_in_reg <= sdram_m_data_in;
        end
    end
end

// Assign control outputs
always_comb begin


		sdram_m_access = grant_active && (mcga_m_access || cpu_m_access);

      //cpu_m_ack = (servingA) && sdram_m_ack;
      //mcga_m_ack = !servingA && sdram_m_ack;

	   sdram_m_addr = servingA ? cpu_m_addr : mcga_m_addr;
		sdram_m_data_out = servingA ? cpu_m_data_out : mcga_m_data_out;
      sdram_m_wr_en = servingA ? cpu_m_wr_en : mcga_m_wr_en;
      sdram_m_bytesel = servingA ? cpu_m_bytesel : mcga_m_bytesel;

 end

assign q_b = (grant_active && !servingA) || (!grant_active && mcga_m_access);
//assign q_b = !servingA;


endmodule