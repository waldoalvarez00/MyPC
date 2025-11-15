// Behavioral simulation model for altsyncram (Altera/Intel FPGA primitive)
// Simplified single-port RAM for testbench use only

`timescale 1ns/1ps

module altsyncram #(
    parameter byte_size = 8,
    parameter clock_enable_input_a = "BYPASS",
    parameter clock_enable_output_a = "BYPASS",
    parameter lpm_hint = "",
    parameter lpm_type = "altsyncram",
    parameter numwords_a = 8192,
    parameter operation_mode = "SINGLE_PORT",
    parameter outdata_aclr_a = "NONE",
    parameter outdata_reg_a = "UNREGISTERED",
    parameter power_up_uninitialized = "FALSE",
    parameter read_during_write_mode_port_a = "NEW_DATA_NO_NBE_READ",
    parameter widthad_a = 13,
    parameter width_a = 16,
    parameter width_byteena_a = 2,
    parameter init_file = ""
)(
    input  [widthad_a-1:0]    address_a,
    input  [width_byteena_a-1:0] byteena_a,
    input                     clock0,
    input  [width_a-1:0]      data_a,
    input                     wren_a,
    output reg [width_a-1:0]  q_a,
    input                     aclr0,
    input                     aclr1,
    input                     address_b,
    input                     addressstall_a,
    input                     addressstall_b,
    input                     byteena_b,
    input                     clock1,
    input                     clocken0,
    input                     clocken1,
    input                     clocken2,
    input                     clocken3,
    input                     data_b,
    output                    eccstatus,
    output                    q_b,
    input                     rden_a,
    input                     rden_b,
    input                     wren_b
);

    // Internal RAM storage
    reg [width_a-1:0] mem [0:numwords_a-1];

    // Initialize memory from file if specified
    integer i;
    initial begin
        // Initialize to zero if no init file
        for (i = 0; i < numwords_a; i = i + 1) begin
            mem[i] = {width_a{1'b0}};
        end

        // Load from init file if specified (MIF format)
        if (init_file != "") begin
            $readmemh(init_file, mem);
        end
    end

    // RAM behavior
    always @(posedge clock0) begin
        if (wren_a) begin
            // Byte-enable write
            if (byteena_a[0])
                mem[address_a][7:0] <= data_a[7:0];
            if (byteena_a[1])
                mem[address_a][15:8] <= data_a[15:8];
        end

        // Read (even if writing, we output new data for NEW_DATA_NO_NBE_READ mode)
        q_a <= mem[address_a];
    end

endmodule
