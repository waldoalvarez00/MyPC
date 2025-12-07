//
// Altera ALTDDIO_OUT Simulation Stub
//
// This stub simulates the behavior of the Altera altddio_out megafunction
// for Verilator simulation. In simulation, it simply outputs the datain_h
// or datain_l value based on clock edges.
//
// Copyright (c) 2024 - MIT License
//

module altddio_out #(
    parameter extend_oe_disable = "OFF",
    parameter intended_device_family = "Cyclone V",
    parameter invert_output = "OFF",
    parameter lpm_hint = "UNUSED",
    parameter lpm_type = "altddio_out",
    parameter oe_reg = "UNREGISTERED",
    parameter power_up_high = "OFF",
    parameter width = 1
) (
    input  [width-1:0] datain_h,
    input  [width-1:0] datain_l,
    input              outclock,
    output [width-1:0] dataout,
    input              aclr,
    input              aset,
    input              oe,
    input              outclocken,
    input              sclr,
    input              sset
);

    // For simulation, simply output the clock itself
    // This approximates DDR behavior where datain_h is output on rising edge
    // and datain_l is output on falling edge
    reg [width-1:0] out_reg;

    always @(posedge outclock or posedge aclr) begin
        if (aclr)
            out_reg <= (power_up_high == "ON") ? {width{1'b1}} : {width{1'b0}};
        else if (outclocken)
            out_reg <= datain_h;
    end

    // For SDRAM clock generation, the typical usage is:
    // datain_h = 0, datain_l = 1, which creates an inverted clock
    // In simulation, we just pass through the clock or its inverse
    assign dataout = (invert_output == "ON") ? ~out_reg : out_reg;

endmodule
