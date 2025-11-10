// Copyright 2025, Waldo Alvarez, https://pipflow.com
module sclock_enable(Clk_M,slow_clk_en);

input Clk_M;
output slow_clk_en;

    reg [31:0]counter=0;
    always @(posedge Clk_M)
    begin
       counter = (counter>=1000)?32'b0:counter+32'b1;
    end
    assign slow_clk_en = (counter == 1000)?1'b1:1'b0;
endmodule

