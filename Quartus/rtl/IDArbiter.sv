
module IDArbiter(
    input clk,
    input reset,

    // Instruction bus
    input [19:1] instr_m_addr,
    output logic [15:0] instr_m_data_in,
    input  [15:0] instr_m_data_out,
    input  instr_m_access,
    output logic instr_m_ack,
    input  instr_m_wr_en,
    input  [1:0] instr_m_bytesel,

    // Data bus
    input [19:1] data_m_addr,
    output logic [15:0] data_m_data_in,
    input  [15:0] data_m_data_out,
    input  data_m_access,
    output logic data_m_ack,
    input  data_m_wr_en,
    input  [1:0] data_m_bytesel,

    // Output bus
    output logic [19:1] q_m_addr,
    input  [15:0] q_m_data_in,
    output logic [15:0] q_m_data_out,
    output logic q_m_access,
    input  q_m_ack,
    output logic q_m_wr_en,
    output logic [1:0] q_m_bytesel,
    output logic q_b
	 
	 //output logic [2:0] current_state only used for debugging
);



    
    // Extended state machine with explicit wait for ack to be raised
    // proper round-robin scheduling
	 
    localparam [2:0] IDLE = 3'b000, SERVING_A = 3'b001, WAIT_A = 3'b010, 
                     SERVING_B = 3'b011, WAIT_B = 3'b100;

    logic last_served_A;
	 logic servingInstr;
	 
    logic [2:0] arb_state;
	 logic grant_active;
	 
	 

    initial begin
        arb_state = IDLE;
        last_served_A = 1'b0;
		  servingInstr= 1'b0;
    end
	 
	 
	 
	 /*
	 
	 
	 try later double flopping
	 
	 
	 // Additional registers for double flopping
    logic servingA_ff1, servingA_ff2;

    // ... [rest of your initializations] ...

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            // Resetting the double flop registers
            servingA_ff1 <= 1'b0;
            servingA_ff2 <= 1'b0;
            // ... [rest of your reset logic] ...
        end else begin
            // First flip-flop
            servingA_ff1 <= servingA;
            // Second flip-flop
            servingA_ff2 <= servingA_ff1;
            // ... [rest of your sequential logic] ...
        end
    end

    // Use servingA_ff2 instead of servingA for the multiplexer control
    always_comb begin
        q_m_addr = servingA_ff2 ? instr_m_addr : data_m_addr;
        // ... [rest of your combinational logic] ...
    end
	 
	 
	 */
	 

    always_ff @(posedge clk or posedge reset) begin
	 
        if (reset) begin
		  
            arb_state <= IDLE;
            last_served_A <= 1'b0;
				servingInstr <= 1'b0;
		      
				
        end else begin
		  
		      //current_state <= arb_state; // Assign the state to output for debugging
				
            case (arb_state)
                IDLE: begin
					 
					     if(last_served_A) begin
						    // Give priority to B
						    if(data_m_access) begin
							   //arb_state <= PRESERVE_B;
								q_m_access <= 1'b1;
						      arb_state <= SERVING_B; 
								servingInstr <= 1'b0;
								grant_active <= 1'b1;
							 end
							 else begin
							   if (instr_m_access) begin
								  arb_state <= SERVING_A;
								  q_m_access <= 1'b1;
								  servingInstr <= 1'b1;
								  grant_active <= 1'b1;
								end
							 end
						  end
						  else begin
						     // Give priority to A
						     if(instr_m_access) begin
							   arb_state <= SERVING_A;
								q_m_access <= 1'b1;
								servingInstr <= 1'b1;
								grant_active <= 1'b1;
							 end
							 else begin
							   if (data_m_access) begin
								  //arb_state <= PRESERVE_B;
								  q_m_access <= 1'b1;
						        arb_state <= SERVING_B; 
								  servingInstr <= 1'b0;
								  grant_active <= 1'b1;
								end
							 end
						  
						  end
						  
						  
                    
						  
                end
					 
					 
					 
                SERVING_A: begin
					     
                    if (q_m_ack) begin
						      last_served_A <= 1'b1;
                        // Give some time to sample the bus
                        
								arb_state <= IDLE; 
								grant_active <= 1'b0;
								q_m_access <= 1'b0;
                    end
                end
					 
					 
                SERVING_B: begin
					     
                    if (q_m_ack) begin
						      last_served_A <= 1'b0;
								
						      // Give some time to sample the bus
                        arb_state <= WAIT_B;
                        arb_state <= IDLE; 
							   
								q_m_access <= 1'b0;
                    end
                end
					 
					 
                 WAIT_B: begin
					  
                        arb_state <= IDLE; 
								grant_active <= 1'b0;
                   
                end
					 
					 
                default: arb_state <= IDLE;
            endcase
        end
    end


// Register ACK outputs to prevent glitches
logic instr_m_ack_reg;
logic data_m_ack_reg;

assign instr_m_ack = instr_m_ack_reg;
assign data_m_ack  = data_m_ack_reg;

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        instr_m_ack_reg <= 1'b0;
        data_m_ack_reg  <= 1'b0;
    end else begin
        instr_m_ack_reg <= grant_active &  servingInstr & q_m_ack & (arb_state != IDLE);
        data_m_ack_reg  <= grant_active & ~servingInstr & q_m_ack & (arb_state != IDLE);
    end
end

// Assign outputs and acks



	always_comb begin



	   q_m_addr = servingInstr ? instr_m_addr : data_m_addr;
					

		q_m_data_out = servingInstr ? instr_m_data_out : data_m_data_out;
      

						 
      q_m_wr_en = servingInstr ? instr_m_wr_en : data_m_wr_en;
					 
					 

      q_m_bytesel = servingInstr ? instr_m_bytesel : data_m_bytesel;

      instr_m_data_in = servingInstr && q_m_ack ? q_m_data_in : 16'b0; //servingA ? sdram_m_data_in : 0;
	 
	 
      data_m_data_in = !servingInstr && q_m_ack ? q_m_data_in : 16'b0;
		

    // Bus busy signal
    
        q_b = grant_active;
    end

endmodule
