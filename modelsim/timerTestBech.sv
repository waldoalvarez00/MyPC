`timescale 1ns/1ps

module Timer_tb;

reg clk;
reg reset;
reg pit_clk;

reg cs;
reg [2:1] data_m_addr;
reg [15:0] data_m_data_in;
wire [15:0] data_m_data_out;
reg [1:0] data_m_bytesel;
reg data_m_wr_en;
reg data_m_access;
wire data_m_ack;

wire intr;
wire speaker_out;
reg speaker_gate_en;

// Instantiate the Timer module
Timer uut(
    .clk(clk),
    .reset(reset),
    .pit_clk(pit_clk),
    .cs(cs),
    .data_m_addr(data_m_addr),
    .data_m_data_in(data_m_data_in),
    .data_m_data_out(data_m_data_out),
    .data_m_bytesel(data_m_bytesel),
    .data_m_wr_en(data_m_wr_en),
    .data_m_access(data_m_access),
    .data_m_ack(data_m_ack),
    .intr(intr),
    .speaker_out(speaker_out),
    .speaker_gate_en(speaker_gate_en)
);

// Clock generation
always #5 clk = ~clk; // Generate a 100MHz clock
always #10 pit_clk = ~pit_clk; // Generate a 50MHz PIT clock

initial begin
    // Initialize inputs
    clk = 0;
    reset = 1;
    pit_clk = 0;
    cs = 0;
    data_m_addr = 0;
    data_m_data_in = 0;
    data_m_bytesel = 0;
    data_m_wr_en = 0;
    data_m_access = 0;
    speaker_gate_en = 0;

    // Reset the system
    #100;
    reset = 0;
    #100;
	
	
	// Step 1: Set up 8253 timer chip for channel 0
    cs = 1;
    data_m_access = 1;
    data_m_addr = 2'b11; // Assuming this addresses the control register
    data_m_wr_en = 1;
    data_m_data_in = 16'b00110110; // Control word for channel 0 setup
    #20; // Wait for the write to complete

    data_m_wr_en = 0;
    #20; // Additional delay before next operation

    // Program Timer0 with a value of zero
    cs = 1; // Enable chip select
    data_m_access = 1; // Enable access
    data_m_addr = 2'b00; // Address for Timer0
    data_m_wr_en = 1; // Enable write operation
    data_m_data_in = 16'b0; // Load value of zero

    // Complete the programming operation
    #20;
    data_m_wr_en = 0;
    cs = 0;
    data_m_access = 0;

    // Additional delay to observe the behavior
    #500;

    // End simulation
    //$stop;
end

endmodule
