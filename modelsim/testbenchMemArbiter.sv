`timescale 1ns / 1ps

module MemArbiter_tb;

    // Inputs
    reg clk;
    reg reset;
    reg [19:1] a_m_addr;
    reg [15:0] a_m_data_out;
    reg a_m_access;
    reg a_m_wr_en;
    reg [1:0] a_m_bytesel;
    reg [19:1] b_m_addr;
    reg [15:0] b_m_data_out;
    reg b_m_access;
    reg b_m_wr_en;
    reg [1:0] b_m_bytesel;
    reg [15:0] q_m_data_in;
    reg q_m_ack;

    // Outputs
    wire [15:0] a_m_data_in;
    wire a_m_ack;
    wire [15:0] b_m_data_in;
    wire b_m_ack;
    wire [19:1] q_m_addr;
    wire [15:0] q_m_data_out;
    wire q_m_access;
    wire q_m_wr_en;
    wire [1:0] q_m_bytesel;
    wire q_b;

    // Instantiate the Unit Under Test (UUT)
    MemArbiter uut (
        .clk(clk), 
        .reset(reset), 
        .a_m_addr(a_m_addr), 
        .a_m_data_in(a_m_data_in), 
        .a_m_data_out(a_m_data_out), 
        .a_m_access(a_m_access), 
        .a_m_ack(a_m_ack), 
        .a_m_wr_en(a_m_wr_en), 
        .a_m_bytesel(a_m_bytesel), 
        .b_m_addr(b_m_addr), 
        .b_m_data_in(b_m_data_in), 
        .b_m_data_out(b_m_data_out), 
        .b_m_access(b_m_access), 
        .b_m_ack(b_m_ack), 
        .b_m_wr_en(b_m_wr_en), 
        .b_m_bytesel(b_m_bytesel), 
        .q_m_addr(q_m_addr), 
        .q_m_data_in(q_m_data_in), 
        .q_m_data_out(q_m_data_out), 
        .q_m_access(q_m_access), 
        .q_m_ack(q_m_ack), 
        .q_m_wr_en(q_m_wr_en), 
        .q_m_bytesel(q_m_bytesel), 
        .q_b(q_b)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Test Cases
    initial begin
        // Initialize Inputs
        clk = 0;
        reset = 1;
        a_m_addr = 0;
        a_m_data_out = 0;
        a_m_access = 0;
        a_m_wr_en = 0;
        a_m_bytesel = 0;
        b_m_addr = 0;
        b_m_data_out = 0;
        b_m_access = 0;
        b_m_wr_en = 0;
        b_m_bytesel = 0;
        q_m_data_in = 0;
        q_m_ack = 0;

        // Wait for global reset
        #100;
        reset = 1;

        // Wait for global reset to release
        #100;
        reset = 0;

        // Request 1: Apply a request on a_m
        a_m_addr = 19'h1A2B3;
        a_m_data_out = 16'hC0DE;
        a_m_access = 1;
        a_m_wr_en = 1;
        a_m_bytesel = 2'b11;
        #20;  // Duration of the request

        // Reset a_m request
        a_m_access = 0;
        #10;  // Time gap before next request

        // Request 2: Apply a request on b_m
        b_m_addr = 19'h4C5D6;
        b_m_data_out = 16'hBEEF;
        b_m_access = 1;
        b_m_wr_en = 0;
        b_m_bytesel = 2'b10;
        #20;  // Duration of the request

        // Reset b_m request
        b_m_access = 0;
        #10;  // Time gap before next request

        // Request 3: Simultaneous request on a_m and b_m
        a_m_addr = 19'h3F4E5;
        a_m_data_out = 16'hFACE;
        a_m_access = 1;
        a_m_wr_en = 0;
        a_m_bytesel = 2'b01;
        b_m_addr = 19'h7A8B9;
        b_m_data_out = 16'hDEAD;
        b_m_access = 1;
        b_m_wr_en = 1;
        b_m_bytesel = 2'b00;
        #20;  // Duration of the request

        // Reset both a_m and b_m requests
        a_m_access = 0;
        b_m_access = 0;
        #10;  // Time gap before finishing

        // Finish the simulation
        #1000;
        $finish;
    end
      
endmodule
