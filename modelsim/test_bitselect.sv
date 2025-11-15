`timescale 1ns/1ps

module test_bitselect;

reg clk;
reg [7:0] test_reg;
reg [2:0] index;

initial begin
    clk = 0;
    forever #5 clk = ~clk;
end

always_ff @(posedge clk) begin
    test_reg[index] <= 1'b1;
end

initial begin
    test_reg = 8'b0;
    index = 3'd0;

    #10;
    $display("After index 0: test_reg = %b (should be 00000001)", test_reg);

    index = 3'd3;
    #10;
    $display("After index 3: test_reg = %b (should be 00001001)", test_reg);

    index = 3'd7;
    #10;
    $display("After index 7: test_reg = %b (should be 10001001)", test_reg);

    $finish;
end

endmodule
