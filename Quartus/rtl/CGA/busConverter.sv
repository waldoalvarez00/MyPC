module busConverter #(
    parameter AW = 14 // Address Width for the memory
)(
    input wire clk,                  // Clock input
    input wire rst,                  // Asynchronous reset, active high
    input wire en,                   // Enable signal for the module
    input wire we,                   // Write enable signal for the bus converter
    input wire [15:0] data_in,       // 16-bit data input for writing to memory
    output reg [15:0] data_out,      // 16-bit data output from reading memory
    input wire [AW-2:0] addr,        // Address input for memory operations
    input wire [1:0] bytesel,        // 2-bit Byte select signal
    output reg [AW-1:0] mem_addr,    // Output address for memory
    input wire [7:0] mem_data_in,    // 8-bit data input from memory (for reads)
    output reg [7:0] mem_data_out,   // 8-bit data output to memory (for writes)
    output reg mem_we,               // Write enable signal for the memory
    output reg mem_en,               // Access enable signal for the memory
    output reg ack,                  // Acknowledgment signal for 8-bit bus operation completion
    output reg bus_ack               // Acknowledgment signal for 16-bit bus operation completion
);

reg [3:0] state; // State for managing read/write operations

// Define states
localparam IDLE = 4'b0000,
           PROCESS_LOW_BYTE = 4'b0001,
           PROCESS_HIGH_BYTE = 4'b0010,
			  PROCESS_HIGH_BYTEW1 = 4'b0100,
           PROCESS_LOW_BYTEW = 4'b0101,
			  PROCESS_LOW_BYTE_WAIT = 4'b0111,
			  COMPLETE = 4'b1001,
			  PROCESS_HIGH_BYTE_WAIT = 4'b1000,
           PROCESS_HIGH_BYTEW = 4'b0110;

// Memory address is directly mapped from input for simplicity
//assign mem_addr = addr[AW-1:0];

always @(posedge clk or posedge rst) begin
    if (rst) begin
	 
        // Reset logic
        data_out <= 0;
        mem_data_out <= 0;
        mem_we <= 0;
        mem_en <= 0;
        ack <= 0;
        bus_ack <= 0;
        state <= IDLE;
		  
		  
    end else begin
        case (state)
            IDLE: begin
                if (en) begin
                    mem_en <= 1; // Enable memory access
                    //bus_ack <= 0; // Clear bus_ack at the start of an operation
                    if (we) begin
						  
						  
                        mem_we <= 1; // Enable memory write
								
                        if (bytesel[0]) begin
                            mem_data_out <= data_in[7:0]; // Prepare low byte for write
									 mem_addr <= {addr, 1'b0};
                            state <= PROCESS_LOW_BYTEW;
                        end
								else if (bytesel[1]) begin
                            mem_data_out <= data_in[15:8]; // Prepare high byte for write if low byte is not selected
									 mem_addr <= {addr, 1'b1};
                            state <= PROCESS_HIGH_BYTEW;
                        end

								
                    end else begin
						      // Read
                        mem_we <= 0; // Disable memory write for read operations
								
								if(bytesel[0]) begin
								  mem_addr <= {addr, 1'b0};
                          state <= PROCESS_LOW_BYTE_WAIT;
								end 
								else if(bytesel[1]) begin
								
								  mem_addr <= {addr, 1'b1};
                          state <= PROCESS_HIGH_BYTE_WAIT;
								
								end
								
								
                    end
                    ack <= 0; // Clear ack during operation
                end else begin
                    mem_we <= 0;
                    mem_en <= 0;
                end
            end
				
				
				
				
				
				
				
				PROCESS_LOW_BYTEW: begin
                
                    // next byte
                    if (bytesel[1]) begin
						  
                        mem_data_out <= data_in[15:8];
								mem_addr <= {addr, 1'b1};
                        state <= PROCESS_HIGH_BYTEW1;
								
                    end else begin
                        mem_we <= 0; // Disable write after processing
                        mem_en <= 0; // Disable memory access after operation
                        state <= IDLE;
                        
                        bus_ack <= 1; // Complete operation for the bus
                    end
                
					 
					 
				end
				
				
				
				
				PROCESS_LOW_BYTE_WAIT: begin
				state <= PROCESS_LOW_BYTE;
				end
				
				PROCESS_HIGH_BYTE_WAIT: begin
				state <= PROCESS_HIGH_BYTE;
				end
				
				
				
            PROCESS_LOW_BYTE: begin
                begin
                    // Reading low byte
                    data_out[7:0] <= mem_data_in;
						  
						  if(bytesel[1]) begin
						  
						    state <= PROCESS_HIGH_BYTE_WAIT;
						  
						    mem_addr <= {addr, 1'b1};
						  
                      
						  
						  end else
						  begin
						  
						    state <= COMPLETE;
                      mem_en <= 0; // Disable memory access after operation
                      ack <= 1; // Complete if only reading low byte
                      bus_ack <= 1; // Complete operation for the bus
						  
						  end
                    
                end
            end
				
				
				
				
				
				
				
				
				
				
				PROCESS_HIGH_BYTEW1: begin
                
                    // High byte write operation completed
                    mem_we <= 0; // Disable write after processing
                    mem_en <= 0; // Disable memory access after operation
                    state <= COMPLETE;
                    
                    bus_ack <= 1; // Complete operation for the bus
                
				
				end
				
				
				
				
				
				
				
				
				
				
				PROCESS_HIGH_BYTEW: begin
                
                    // High byte write operation completed
                    mem_we <= 0; // Disable write after processing
                    mem_en <= 0; // Disable memory access after operation
                    state <= COMPLETE;
                    ack <= 1; // Write operation complete for high byte
                    bus_ack <= 1; // Complete operation for the bus
                
            end
				
				
				
				
				
				
				
				
            PROCESS_HIGH_BYTE: begin
                
                    // Reading high byte
                    data_out[15:8] <= mem_data_in;
                    mem_en <= 0; // Disable memory access after operation
                    state <= COMPLETE;
                    
                    bus_ack <= 1; // Complete operation for the bus
                
            end
				
				COMPLETE: begin
                
                    
                    mem_en <= 0; // Disable memory access after operation
                    state <= IDLE;
                    
                    bus_ack <= 0; // Complete operation for the bus
                
            end
				
				
				
        endcase
    end
end

endmodule
