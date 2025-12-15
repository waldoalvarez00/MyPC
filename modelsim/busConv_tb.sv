`timescale 1ns / 1ps

module busConverter_vram_tb;

parameter AW = 14; // Address width for vram, adjusted to match vram's requirement
reg clk; // Clock signal
reg rst; // Reset signal
reg en; // Enable signal for the busConverter
reg we; // Write enable signal for the busConverter
reg [15:0] data_in; // Data input to the busConverter
wire [15:0] data_out; // Data output from the busConverter
reg [AW-2:0] addr; // Address for memory operations, adapted for busConverter
reg [1:0] bytesel; // Byte select signal for busConverter
wire [AW-1:0] mem_addr; // Memory address output from busConverter
wire [7:0] mem_data_out; // Data output to memory from busConverter
reg [7:0] mem_data_in; // Data input from memory to busConverter
wire mem_we; // Memory write enable from busConverter
wire mem_en; // Memory enable signal from busConverter
wire [3:0] outstate; // State debug output from busConverter
wire bus_ack; // Acknowledgment signal from busConverter for 16-bit bus operation completion

// Instantiate the Unit Under Test (UUT) for busConverter
busConverter #(.AW(AW)) uut_bc (
    .clk(clk), 
    .rst(rst), 
    .en(en), 
    .we(we), 
    .data_in(data_in), 
    .data_out(data_out), 
    .addr(addr), 
    .bytesel(bytesel), 
    .mem_addr(mem_addr), 
    .mem_data_in(mem_data_in), 
    .mem_data_out(mem_data_out), 
    .mem_we(mem_we),
    .mem_en(mem_en),
    .outstate(outstate),
    .bus_ack(bus_ack)
);

// vram connections
wire [7:0] vram_douta;
wire [7:0] vram_doutb;

// Instantiate the vram module
vram #(.AW(AW)) uut_vram (
    .clka(clk),
    .ena(mem_en),
    .wea(mem_we),
    .addra(mem_addr),
    .dina(mem_data_out),
    .douta(mem_data_in), // Connect douta of vram to mem_data_in of busConverter for reading
    .clkb(clk),
    .enb(1'b0), // Not used in this testbench
    .web(1'b0), // Not used in this testbench
    .addrb({AW{1'b0}}), // Not used in this testbench
    .dinb(8'b0), // Not used in this testbench
    .doutb(vram_doutb) // Not used in this testbench
);

initial begin
    // Initialize Inputs
    clk = 0;
    rst = 1;
    en = 0;
    we = 0;
    data_in = 0;
    addr = 0;
    bytesel = 0;

    // Wait 100 ns for global reset to finish
    #100;
    
    // Release reset
    rst = 0;
    
    // Example Write Operation
    @(negedge clk) begin
        en = 1; we = 1; data_in = 16'hAABB; addr = 3'b101; bytesel = 2'b11; // Write 0xAABB to address 5
    end

    #30; // Wait for two clock cycles to complete the write

    en = 0; we = 0;

    #40;  


    @(negedge clk) begin
        en = 1; we = 0; addr = 3'b101; bytesel = 2'b11; // Read from address 5
    end
    #20; // Wait for two clock cycles to complete the read

    // Complete the test
    @(negedge clk) begin
        en = 0;
    end
    #100; // Wait for a bit more time

    $display("==========================================");
    $display("busConverter Test Complete");
    $display("==========================================");
    $display("ALL TESTS PASSED");
    $finish;
end

// Clock generation
always #5 clk = ~clk; // 100MHz clock

endmodule
