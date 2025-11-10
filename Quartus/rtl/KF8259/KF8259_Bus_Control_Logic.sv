// Copyright 2025, Waldo Alvarez, https://pipflow.com
//
// KF8259_Bus_Control_Logic
// Data Bus Buffer & Read/Write Control Logic
//
// Written by Kitune-san
//


// Decodes partially signals from data bus comming from CPU
// Later control unit will decide according to state

`default_nettype none

module KF8259_Bus_Control_Logic (
    input   wire                clock,
    input   wire                reset,

    input   wire                chip_select,
    input   wire                read_enable,
    input   wire                write_enable,
    input   wire                address,
    input   wire        [7:0]   data_bus_in,
     
    output  wire                ack,

    // Internal Bus
    output  logic   [7:0]       internal_data_bus,
    output  wire                write_initial_command_word_1,
    output  wire                write_initial_command_word_2_to_4,
    output  wire                write_operation_control_word_1,
    output  wire                write_operation_control_word_2,
    output  wire                write_operation_control_word_3,
    output  wire                read
);




   wire write;
   
	
   //
   // Write Control
   //
	
	
    
   assign write = chip_select & write_enable;
	   
   
   
   always_comb begin
   
      if(write)
	    internal_data_bus = data_bus_in;
	  else
	    internal_data_bus = 8'b0;
   
   end


    //
    // Read Control
    //
	
	// ICW1 is done with bit 4 set to 1
	assign write_initial_command_word_1      = write & ~address & data_bus_in[4];
	
	// Rest ICW 2-4 have the bit 4 at zero
	assign write_initial_command_word_2_to_4 = write & address;
	
	// Same logic but selected by another state
	assign write_operation_control_word_1    = write & address;
	
	
	
	// OCW2 is distinguished from OCW3 by bit 3 set to 1 (both have 4th bit zero)
	assign write_operation_control_word_2    = write & ~address & ~data_bus_in[4] & ~data_bus_in[3];
    assign write_operation_control_word_3    = write & ~address & ~data_bus_in[4] &  data_bus_in[3];
     
    assign read = read_enable & chip_select;
     
    assign ack = (read_enable | write_enable) & chip_select;

endmodule

