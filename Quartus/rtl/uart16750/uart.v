module uart
(
	input            clk,
	input            reset,

	input      [2:0] address,
	input            write,
	input      [7:0] writedata,
	input            read,
	output reg [7:0] readdata,
	
	output reg       ack,
	
	input            cs,

	input            br_clk,
	input            rx,
	output           tx,
	input            cts_n,
	input            dcd_n,
	input            dsr_n,
	input            ri_n,
	output           rts_n,
	output           br_out,
	output           dtr_n,

	output           irq
);

wire [7:0] data;

reg        ack_next; // Register to hold the next state of ack signal

// Logic to generate ack signal for one clock cycle
always @(posedge clk or posedge reset) begin
    if (reset) begin
        ack <= 1'b0;
        ack_next <= 1'b0;
    end else begin
        ack <= ack_next; // Update ack with the value prepared in the last cycle
        // Set ack_next high if there's a read or write operation
        ack_next <= (read | write) & cs;
    end
end

always @(posedge clk) if(read & cs) readdata <= data;

uart_16750 uart_16750
(
	.CLK(clk),
	.RST(reset),
	.BAUDCE(br_clk),
	.CS(cs & (read | write)),
	.WR(write),
	.RD(read),
	.A(address),
	.DIN(writedata),
	.DOUT(data),
	.RCLK(br_out),
	
	.BAUDOUTN(br_out),

	.RTSN(rts_n),
	.DTRN(dtr_n),
	.CTSN(cts_n),
	.DSRN(dsr_n),
	.DCDN(dcd_n),
	
	.RIN(ri_n),	
	.SIN(rx),
	.SOUT(tx),

	.INT(irq)

);

endmodule
