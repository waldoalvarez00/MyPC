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


    //
    // Write Control
    //
    always_ff @(posedge reset or posedge clock) begin
        if (reset) begin
            internal_data_bus <= 8'b00000000;
			   prev_write_enable <= 1'b0;
			   prev_chip_select <= 1'b0;
        end else begin

		    if (write_enable & chip_select)
              internal_data_bus <= data_bus_in;

		    if (!chip_select)
              prev_write_enable <= 1'b0;
		    else
              prev_write_enable <= write_enable;

		    // Track chip_select transitions
          prev_chip_select <= chip_select;

		end

    end

	// Generate ack signal - combinational for fast response
    // Ack is asserted whenever chip_select is high with read or write enabled
    assign ack = (write_enable | read_enable) & chip_select;

    
	
    assign write_flag = prev_write_enable & ~write_enable;

    always_ff @(posedge reset or posedge clock) begin
        if (reset)
            stable_address <= 2'b00;
        else
            stable_address <= address;
    end

    // Generate write request flags
    assign write_port_a  = (stable_address == `ADDRESS_PORT_A ) & write_flag & chip_select;
    assign write_port_b  = (stable_address == `ADDRESS_PORT_B ) & write_flag & chip_select;
    assign write_port_c  = (stable_address == `ADDRESS_PORT_C ) & write_flag & chip_select;
    assign write_control = (stable_address == `ADDRESS_CONTROL) & write_flag & chip_select;

    // Debug signals for verification
    `ifndef verilator
    logic debug_write_control;
    always @(posedge clock) debug_write_control <= write_control;
    `endif

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

