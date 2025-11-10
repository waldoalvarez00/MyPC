// Copyright 2025, Waldo Alvarez, https://pipflow.com
module vram #(parameter AW=16)
(
  input clka,
  input ena,
  input wea,
  input [AW-1:0] addra,
  input [7:0] dina,
  output reg [7:0] douta,
  input clkb,
  input enb,
  input web,
  input [AW-1:0] addrb,
  input [7:0] dinb,
  output reg [7:0] doutb
);

// Use explicit [0:N-1] ordering for IEEE 1364-2005 compatibility
reg [7:0] vram[0:(2**AW)-1];

// Conditional initialization for Icarus vs Quartus compatibility
`ifdef ICARUS
  initial $readmemh("splash.hex", vram, 0, (2**AW)-1);
`else
  initial $readmemh("splash.hex", vram);
`endif

always @(posedge clka)
  if (ena) begin
		if (wea) begin
			vram[addra] <= dina;
		end else begin
			douta <= vram[addra];
		end
  end
		
			
always @(posedge clkb)
  if (enb)
		if (web)
			vram[addrb] <= dinb;
		else
			doutb <= vram[addrb];

endmodule