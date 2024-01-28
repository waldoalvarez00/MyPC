//
// sdram.v
//
// sdram controller implementation for the MiST board
// http://code.google.com/p/mist-board/
// 
// Copyright (c) 2013 Till Harbaum <till@harbaum.org>
// Copyright (c) 2024 Waldo Alvarez https://pipflow.com
// 
// This source file is free software: you can redistribute it and/or modify 
// it under the terms of the GNU General Public License as published 
// by the Free Software Foundation, either version 3 of the License, or 
// (at your option) any later version. 
// 
// This source file is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of 
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the 
// GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License 
// along with this program.  If not, see <http://www.gnu.org/licenses/>. 
//

module sdramtut6 (

	// interface to the MT48LC16M16 chip
	inout [15:0]  		    sd_data,    // 16 bit bidirectional data bus
	output [12:0]		    sd_addr,    // 13 bit multiplexed address bus
	
	output  		          sd_dqmh,    // two byte masks ?
	output  		          sd_dqml,    // two byte masks ?

	output [1:0] 		    sd_ba,      // two banks
	output 				    sd_cs,      // a single chip select
	output 				    sd_we,      // write enable
	output 				    sd_ras,     // row address select
	output 				    sd_cas,     // columns address select

	// cpu/chipset interface
	input 		 		    init,       // init signal after FPGA config to initialize RAM
	input 		 		    clk,        // sdram is accessed at up to 128MHz
	
	
	output reg            configdone, // SDRAM configuration was completed
	input [1:0]           bytesel,
	
	input      [15:0]     din,        // data input from chipset/cpu
	output reg [15:0]     dout,       // data output to chipset/cpu
	output reg            ack,        // Acknowledge signal
	input      [24:0]     addr,       // 25 bit byte address
	input 		 		    oe,         // cpu/chipset requests read
	input 		 		    we          // cpu/chipset requests write
);

// Add a counter for the ack signal duration
reg [1:0] ack_counter;

// no burst configured
localparam RASCAS_DELAY   = 3'd3;   // tRCD>=20ns -> 2 cycles@64MHz
localparam BURST_LENGTH   = 3'b000; // 000=none, 001=2, 010=4, 011=8
localparam ACCESS_TYPE    = 1'b0;   // 0=sequential, 1=interleaved
localparam CAS_LATENCY    = 3'd2;   // 2/3 allowed
localparam OP_MODE        = 2'b00;  // only 00 (standard operation) allowed
localparam NO_WRITE_BURST = 1'b1;   // 0= write burst enabled, 1=only single access write

localparam MODE = { 3'b000, NO_WRITE_BURST, OP_MODE, CAS_LATENCY, ACCESS_TYPE, BURST_LENGTH}; 

// ---------------------------------------------------------------------
// ------------------------ cycle state machine ------------------------
// ---------------------------------------------------------------------

localparam STATE_IDLE      = 4'd0;   // first state in cycle
localparam STATE_CMD_START = 4'd1;   // state in which a new command can be started

// 4 command can be continued
localparam STATE_CMD_CONT  = STATE_CMD_START  + RASCAS_DELAY - 4'd1;
localparam STATE_LAST      = 4'd7;   // last state in cycle

localparam RAM_CLK          = 70000000;

localparam REFRESH_PERIOD   = (RAM_CLK / (16 * 8192));

reg  [9:0] sd_refresh = 10'd0;

reg [3:0] q /* synthesis noprune */;

initial begin

	 ack_counter = 0; // Initialize ack counter
	 configdone = 0;
	 q = 4'd0;
end




reg [2:0] q2 /* synthesis noprune */;


always @(posedge clk) begin

			q2 <= q2 + 3'd1; // Overflows on 8
end




// ---------------------------------------------------------------------
// --------------------------- startup/reset ---------------------------
// ---------------------------------------------------------------------

// wait 1ms (32 clkref cycles) after FPGA config is done before going
// into normal operation. Initialize the ram in the last 16 reset cycles (cycles 15-0)
reg [4:0] reset;
always @(posedge clk) begin
	if(init)	begin
	reset <= 5'h1f;
	
	end
	else if((q2 == STATE_LAST) && (reset != 0))
		reset <= reset - 5'd1;
end

// ---------------------------------------------------------------------
// ------------------ generate ram control signals ---------------------
// ---------------------------------------------------------------------

// all possible commands
localparam CMD_INHIBIT         = 4'b1111;
localparam CMD_NOP             = 4'b0111;
localparam CMD_ACTIVE          = 4'b0011;
localparam CMD_READ            = 4'b0101;
localparam CMD_WRITE           = 4'b0100;
localparam CMD_BURST_TERMINATE = 4'b0110;
localparam CMD_PRECHARGE       = 4'b0010;
localparam CMD_AUTO_REFRESH    = 4'b0001;
localparam CMD_LOAD_MODE       = 4'b0000;

reg [3:0] sd_cmd;   // current command sent to sd ram

// drive control signals according to current command
assign sd_cs  = sd_cmd[3];
assign sd_ras = sd_cmd[2];
assign sd_cas = sd_cmd[1];
assign sd_we  = sd_cmd[0];

assign sd_data = (oe & we)? din:16'bZZZZZZZZZZZZZZZZ;


always @(posedge clk) begin


	//sd_cmd <= CMD_INHIBIT;
	sd_cmd <= CMD_NOP; // Documentation says is a NOP
	
	
	
	if (ack_counter > 0) begin
        ack_counter <= ack_counter - 1; // Decrement ack counter
    end else begin
        ack <= 0; // Reset ack if counter is zero
    end
	 
	 

	if(reset != 0) begin
	
	   // Chip Initialization
		
		if(q2 == STATE_IDLE) begin
			if(reset == 13)  sd_cmd <= CMD_PRECHARGE;
			if(reset ==  2)  sd_cmd <= CMD_LOAD_MODE;
		end
		
		
		if(reset == 1) begin
		
		  
		  configdone <= 1'b1;
		  q <= 4'd0;
		
		end
		
		
		
	end else begin
	
	   sd_refresh <= sd_refresh + 9'd1; // increment refresh count
	
	   case (q)
		
		STATE_IDLE: begin
							if(oe) begin
								  
								  dout <= 16'd0;
								  
								  
								  if (sd_refresh > REFRESH_PERIOD) 
					           begin 
						          // this is the auto refresh code.
						          // it kicks in so that 8192 auto refreshes are 
						          // issued in a 64ms period. Other bus operations 
						          // are stalled during this period.
						
						          sd_refresh		 <= 0;
						          sd_cmd <= CMD_AUTO_REFRESH;
								    q <= 4'd8;
						
					           end
								  else 
								  begin
								    sd_cmd <= CMD_ACTIVE;
								    q <= 4'd1;
								  end
								  
								  
								  
								end
								else begin
								
								  if (sd_refresh > REFRESH_PERIOD) 
					           begin 
								  
						          // auto refresh code.
						          
						          sd_refresh		 <= 0;
						          sd_cmd <= CMD_AUTO_REFRESH;
								    q <= 4'd8;
						
					           end
								
								  
								end
								
							
		            end
						
		1: begin
		     q <= 4'd2;
		   end
			
		2: begin
		     q <= STATE_CMD_CONT;
		   end
						
		STATE_CMD_CONT: begin
								if(oe && we)		 sd_cmd <= CMD_WRITE;
								else if(oe)  sd_cmd <= CMD_READ;
								q <= 4'd4;
		                end
		
		
		4: begin
		    q <= 4'd5;
		   end
			
		5: begin
		    q <= 4'd6;
		   end
			
		6: begin
		     q <= 4'd7;
			  dout <= sd_data[15:0];
			  ack <= 1'b1;           // Assert ack signal on completion of read/write
           ack_counter <= 2;      // Set ack counter to keep ack high for 2 cycles
		   end
			
			
		7: begin
		    q <= STATE_IDLE;
		   end
			
			
			
		8: begin
			  // Sends a series of NOPs until refresh is completed
		     q <= 4'd9;
		   end
			
		9: begin
		     q <= 4'd10;
		   end
			
		10: begin
		     q <= 4'd11;
		   end
			
		11: begin
		     q <= 4'd12;
		   end
			
			
		12: begin
		     q <= 4'd13;
		   end
			
		13: begin
		     q <= 4'd14;
		   end
			
		14: begin
		     q <= STATE_IDLE;
		   end
			
		endcase
		
		
		
		
	end
	

	
end
	
wire [12:0] reset_addr = (reset == 13)?13'b0010000000000:MODE;
	
	
wire [1:0] byte_mask = we ? ~bytesel : 2'b00; // Active low masks: 0 enables writing to the corresponding byte

/*
wire [12:0] run_addr = 
	(q == STATE_CMD_START)?addr[20:8]:{ 4'b0010, addr[23], addr[7:0]};*/

	
// Updated run_addr to include byte selection logic
wire [12:0] run_addr = (q == STATE_CMD_START) ? addr[20:8] :
                       {byte_mask, 2'b10, addr[23], addr[7:0]}; // Include byte_mask in address ?!?
							  
							  

assign sd_addr = (reset != 0)?reset_addr:run_addr;

assign sd_ba = addr[22:21];

assign sd_dqmh = 1'b0;
assign sd_dqml = 1'b0;


// lines changed ???

//assign sd_dqm = we ? ~bytesel[1:0] : 2'b00;

//assign sd_dqmh = we ? ~bytesel[1] : 1'b0;
//assign sd_dqml = we ? ~bytesel[0] : 1'b0;

//assign sd_dqm[0] = we ? ~bytesel[1] : 1'b0;
//assign sd_dqm[1] = we ? ~bytesel[0] : 1'b0;

//assign sd_dqm[0] = ~bytesel[1]; //2'b00;
//assign sd_dqm[1] = ~bytesel[0];


endmodule
