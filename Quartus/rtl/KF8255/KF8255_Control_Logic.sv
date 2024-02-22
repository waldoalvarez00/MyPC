//
// KF8255_Control_Logic
// Data Bus Buffer & Read/Write Control Logic
//
// Written by Kitune-san
//

`include "KF8255_Definitions.svh"

module KF8255_Control_Logic (
    // Bus
    input   wire            clock,
    input   wire            reset,
    input   wire            chip_select,
    input   wire            read_enable,
    input   wire            write_enable,
    input   wire    [1:0]   address,
    input   wire    [7:0]   data_bus_in,

    // Control Signals
    output  logic   [7:0]   internal_data_bus,
    output  logic           write_port_a,
    output  logic           write_port_b,
    output  logic           write_port_c,
    output  logic           write_control,
    output  logic           read_port_a,
    output  logic           read_port_b,
    output  logic           read_port_c,
	
	 output  logic           ack
);


    //
    // Internal Signals
    //
    logic           prev_write_enable;
    logic           write_flag;
    logic   [2:0]   stable_address;
	
	 logic           prev_chip_select;
    logic           operation_initiated;


    //
    // Write Control
    //
    always_ff @(posedge reset or posedge clock) begin
        if (reset) begin
            internal_data_bus <= 8'b00000000;
			   prev_write_enable <= 1'b0;
        end else begin
		
		    if (write_enable & chip_select)
              internal_data_bus <= data_bus_in;
			
		    if (!chip_select)
              prev_write_enable <= 1'b0;
		    else
              prev_write_enable <= write_enable;
		
		    // Track chip_select transitions
          prev_chip_select <= chip_select;

          // Detect operation initiation
          operation_initiated <= (write_enable | read_enable) & chip_select & ~prev_chip_select;
			
		end
        
    end
	
	// Generate ack signal
    // Ack is asserted for one clock cycle after an operation is initiated
    always_ff @(posedge clock or posedge reset) begin
        if (reset)
            ack <= 1'b0;
        else
            ack <= operation_initiated;
    end

    
	
    assign write_flag = prev_write_enable & ~write_enable;

    always_ff @(posedge reset or posedge clock) begin
        if (reset)
            stable_address <= 2'b00;
        else
            stable_address <= address;
    end

    // Generate write request flags
    assign write_port_a  = (stable_address == `ADDRESS_PORT_A ) & write_flag;
    assign write_port_b  = (stable_address == `ADDRESS_PORT_B ) & write_flag;
    assign write_port_c  = (stable_address == `ADDRESS_PORT_C ) & write_flag;
    assign write_control = (stable_address == `ADDRESS_CONTROL) & write_flag;


    //
    // Read Control
    //
    always_comb begin
        read_port_a = 1'b0;
        read_port_b = 1'b0;
        read_port_c = 1'b0;

        if (read_enable  & chip_select) begin
            // Generate read request flags
            case (address)
                `ADDRESS_PORT_A : read_port_a = 1'b1;
                `ADDRESS_PORT_B : read_port_b = 1'b1;
                `ADDRESS_PORT_C : read_port_c = 1'b1;
                default         : read_port_a = 1'b1;
            endcase
        end
    end
endmodule

