//
// sdram.v
//
// Static RAM controller implementation using SDRAM MT48LC16M16A2
//

//
// v2.1 - Add universal 8/16 bit mode.
// v2.2 - Support for SDRAM v2
//

module sdram2cv
(
   input             init,        // reset to initialize RAM
   input             clk,         // clock ~100MHz
                                  //
                                  // SDRAM_* - signals to the MT48LC16M16 chip
   inout  reg [15:0] SDRAM_DQ,    // 16 bit bidirectional data bus
   output reg [12:0] SDRAM_A,     // 13 bit multiplexed address bus
   output reg        SDRAM_DQML,  // two byte masks
   output reg        SDRAM_DQMH,  // 
   output reg  [1:0] SDRAM_BA,    // two banks
   output            SDRAM_nCS,   // a single chip select
   output            SDRAM_nWE,   // write enable
   output            SDRAM_nRAS,  // row address select
   output            SDRAM_nCAS,  // columns address select
   output            SDRAM_CKE,   // clock enable
                                  //
   input       [1:0] wtbt,        // 16bit mode:  bit1 - write high byte, bit0 - write low byte,
                                  // 8bit mode:  2'b00 - use addr[0] to decide which byte to write
                                  // Ignored while reading.
                                  //
   input      [24:0] addr,        // 25 bit address for 8bit mode. addr[0] = 0 for 16bit mode for correct operations.
   output     [15:0] dout,        // data output to cpu
   input      [15:0] din,         // data input from cpu
   input             we,          // cpu requests write
   input             rd,          // cpu requests read
   output reg        ready,       // dout is valid. Ready to accept new read/write.
	output reg        ack,         // ack operation is done (new)
	output reg        configdone,
	
	// DEBUG OUTPUT
	output reg        [5:0]staterpt
);

assign SDRAM_nCS  = command[3];
assign SDRAM_nRAS = command[2];
assign SDRAM_nCAS = command[1];
assign SDRAM_nWE  = command[0];
assign SDRAM_CKE  = 1;
assign {SDRAM_DQMH,SDRAM_DQML} = SDRAM_A[12:11];

assign dout       = latched ? data_l : data_d;

// no burst configured
localparam BURST_LENGTH        = 3'b000;   // 000=1, 001=2, 010=4, 011=8
localparam ACCESS_TYPE         = 1'b0;     // 0=sequential, 1=interleaved
localparam CAS_LATENCY         = 3'd2;     // 2 for < 100MHz, 3 for >100MHz
localparam OP_MODE             = 2'b00;    // only 00 (standard operation) allowed
localparam NO_WRITE_BURST      = 1'b1;     // 0= write burst enabled, 1=only single access write
localparam MODE                = {3'b000, NO_WRITE_BURST, OP_MODE, CAS_LATENCY, ACCESS_TYPE, BURST_LENGTH};

localparam sdram_startup_cycles= 14'd12100;// 100us, plus a little more, @ 100MHz
localparam cycles_per_refresh  = 14'd780;  // (64000*100)/8192-1 Calc'd as (64ms @ 100MHz)/8192 rose
localparam startup_refresh_max = 14'b11111111111111;

// SDRAM commands
localparam CMD_INHIBIT         = 4'b1111; // 15
localparam CMD_NOP             = 4'b0111; //  7
localparam CMD_ACTIVE          = 4'b0011;
localparam CMD_READ            = 4'b0101;
localparam CMD_WRITE           = 4'b0100;
localparam CMD_BURST_TERMINATE = 4'b0110;
localparam CMD_PRECHARGE       = 4'b0010;
localparam CMD_AUTO_REFRESH    = 4'b0001;
localparam CMD_LOAD_MODE       = 4'b0000;

reg [13:0] refresh_count = startup_refresh_max - sdram_startup_cycles;
reg  [3:0] command = CMD_INHIBIT;
reg [24:0] save_addr;

reg        latched;
reg [15:0] data;
wire[15:0] data_l = save_addr[0] ? {data[7:0],     data[15:8]}     : {data[15:8],     data[7:0]};
wire[15:0] data_d = save_addr[0] ? {SDRAM_DQ[7:0], SDRAM_DQ[15:8]} : {SDRAM_DQ[15:8], SDRAM_DQ[7:0]};

typedef enum
{
	STATE_STARTUP ,
	STATE_OPEN_1 , STATE_OPEN_2 ,
	STATE_WRITE ,
	STATE_READ ,
	STATE_IDLE ,	  STATE_IDLE_1 , STATE_IDLE_2 , STATE_IDLE_3 ,
	STATE_IDLE_4 , STATE_IDLE_5 , STATE_IDLE_6 , STATE_IDLE_7 
} state_t;


/*
reg [3:0] state = STATE_STARTUP;
initial begin
    staterpt = 13;  // Set initial value for simulation
end
*/

always @(posedge clk) begin
	reg old_we, old_rd;
	reg [CAS_LATENCY:0] data_ready_delay;

	reg [15:0] new_data;
	reg  [1:0] new_wtbt;
	reg        new_we;
	reg        new_rd;
	reg        save_we = 1;
	
	reg ack_set;
	//reg state_is_read_or_write; // Register to hold if the current state is read or write

	state_t state = STATE_STARTUP;
	staterpt = 13;

	command <= CMD_NOP;
	refresh_count  <= refresh_count+1'b1;

	data_ready_delay <= {1'b0, data_ready_delay[CAS_LATENCY:1]};

	// make it ready 1T in advance
	if(data_ready_delay[1]) {latched, ready, ack_set } <= {1'b0, 1'b1, 1'b1};
	if(data_ready_delay[0]) {latched, data}  <= {1'b1, SDRAM_DQ};

	
	
   //state_is_read_or_write <= (state == STATE_READ || state == STATE_WRITE);
	 
	case(state)
		STATE_STARTUP: begin
			//------------------------------------------------------------------------
			//-- This is the initial startup state, where we wait for at least 100us
			//-- before starting the start sequence
			//-- 
			//-- The initialisation is sequence is 
			//--  * de-assert SDRAM_CKE
			//--  * 100us wait, 
			//--  * assert SDRAM_CKE
			//--  * wait at least one cycle, 
			//--  * PRECHARGE
			//--  * wait 2 cycles
			//--  * REFRESH, 
			//--  * tREF wait
			//--  * REFRESH, 
			//--  * tREF wait 
			//--  * LOAD_MODE_REG 
			//--  * 2 cycles wait
			//------------------------------------------------------------------------
			SDRAM_DQ   <= 16'bZZZZZZZZZZZZZZZZ;
			SDRAM_A    <= 0;
			SDRAM_BA   <= 0;

			// All the commands during the startup are NOPS, except these
			if(refresh_count == startup_refresh_max-31) begin
				// ensure all rows are closed
				command     <= CMD_PRECHARGE;
				SDRAM_A[10] <= 1;  // all banks
				SDRAM_BA    <= 2'b00;
			end else if (refresh_count == startup_refresh_max-23) begin
				// these refreshes need to be at least tREF (66ns) apart
				command     <= CMD_AUTO_REFRESH;
			end else if (refresh_count == startup_refresh_max-15) 
				command     <= CMD_AUTO_REFRESH;
			else if (refresh_count == startup_refresh_max-7) begin
				// Now load the mode register
				command     <= CMD_LOAD_MODE;
				SDRAM_A     <= MODE;
			end

			//------------------------------------------------------
			//-- if startup is complete then go into idle mode,
			//-- get prepared to accept a new command, and schedule
			//-- the first refresh cycle
			//------------------------------------------------------
			if(!refresh_count) begin
				state   <= STATE_IDLE;
				staterpt <= 0;
				configdone <= 1;
				ready   <= 1;
				refresh_count <= 0;
			end
		end

		STATE_IDLE_7: 
		begin
		state <= STATE_IDLE_6;
		staterpt <= 6;
		end
		
		STATE_IDLE_6:
		begin
		state <= STATE_IDLE_5;
		staterpt <= 5;
		end
		
		STATE_IDLE_5: 
		begin
		state <= STATE_IDLE_4;
		staterpt <= 4;
		end
		
		STATE_IDLE_4: 
		begin
		state <= STATE_IDLE_3;
		staterpt <= 3;
		end
		
		STATE_IDLE_3: 
		begin
		state <= STATE_IDLE_2;
		staterpt <= 2;
		end
		
		STATE_IDLE_2: 
		begin
		state <= STATE_IDLE_1;
		staterpt <= 1;
		end
		
		STATE_IDLE_1: begin
			SDRAM_DQ   <= 16'bZZZZZZZZZZZZZZZZ;
			state      <= STATE_IDLE;
			staterpt <= 0;
			// mask possible refresh to reduce colliding.
			if(refresh_count > cycles_per_refresh) begin
            //------------------------------------------------------------------------
            //-- Start the refresh cycle. 
            //-- This tasks tRFC (66ns), so 6 idle cycles are needed @ 100MHz
            //------------------------------------------------------------------------
				state    <= STATE_IDLE_7;
				staterpt <= 7;
				
				command  <= CMD_AUTO_REFRESH;
				refresh_count <= refresh_count - cycles_per_refresh + 1'd1;
			end
		end

		STATE_IDLE: begin
		
		   //if(state_is_read_or_write) begin
         //       ack_set <= 1; // Set ack_set when transitioning from read/write to idle
         //end
			
			// Priority is to issue a refresh if one is outstanding
			if(refresh_count > (cycles_per_refresh<<1))
			begin
			  state <= STATE_IDLE_1;
			  staterpt <= 1;
			end
			else if(new_rd | new_we) begin
				new_we   <= 0;
				new_rd   <= 0;
				save_addr<= addr;
				save_we  <= new_we;
				state    <= STATE_OPEN_1;
				staterpt    <= 12;
				command  <= CMD_ACTIVE;
				SDRAM_A  <= addr[13:1];
				SDRAM_BA <= addr[24:23];
			end
		end

		// ACTIVE-to-READ or WRITE delay >20ns (-75)
		STATE_OPEN_1: begin
			SDRAM_A     <= '1;
			state       <= STATE_OPEN_2;
			staterpt       <= 11;
		end
		STATE_OPEN_2: begin
			SDRAM_A     <= {save_we & (new_wtbt ? ~new_wtbt[1] : ~save_addr[0]), save_we & (new_wtbt ? ~new_wtbt[0] :  save_addr[0]), 2'b10, save_addr[22:14]};
			state       <= save_we ? STATE_WRITE : STATE_READ;
			staterpt    <= save_we ? 10 : 9;
		end

		STATE_READ: begin
			state       <= STATE_IDLE_5;
			staterpt       <= 5;
			command     <= CMD_READ;
			SDRAM_DQ    <= 16'bZZZZZZZZZZZZZZZZ;

			// Schedule reading the data values off the bus
			data_ready_delay[CAS_LATENCY] <= 1;
		end

		STATE_WRITE: begin
			state       <= STATE_IDLE_5;
			staterpt    <= 5;
			command     <= CMD_WRITE;
			SDRAM_DQ    <= new_wtbt ? new_data : {new_data[7:0], new_data[7:0]};
			ready       <= 1;
			ack_set     <= 1;
		end
	endcase
	
	// Logic to handle the ack output
    if(ack_set) begin
        ack <= 1; // Set ack high when ack_set is high
        ack_set <= 0; // Reset ack_set for next operation
    end else begin
        ack <= 0; // Ensure ack is low in all other cases
    end

	if(init) begin
		state <= STATE_STARTUP;
		staterpt <= 14;
		refresh_count <= startup_refresh_max - sdram_startup_cycles;
		configdone <= 0; // Initialize configdone to 0 on reset
		ack <= 0;
		ack_set <= 0;
	end

	old_we <= we;
	if(we & ~old_we) {ready, new_we, new_data, new_wtbt} <= {1'b0, 1'b1, din, wtbt};

	old_rd <= rd;
	if(rd & ~old_rd) begin
		if(ready & ~save_we & (save_addr[24:1] == addr[24:1])) save_addr <= addr;
			else {ready, new_rd} <= {1'b0, 1'b1};
	end
end

endmodule