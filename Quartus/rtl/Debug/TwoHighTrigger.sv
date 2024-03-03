module TwoHighTrigger(
    input wire [7:0] inputs, // 8-bit input, each bit represents an input signal
    output wire trigger      // Trigger output
);

// Use bitwise operations and intermediate sums to optimize counting for 8 inputs
wire [3:0] count; // 4 bits to handle sum up to 8

// Simplified addition for 8 inputs
assign count = (inputs[0] + inputs[1]) + (inputs[2] + inputs[3]) +
               (inputs[4] + inputs[5]) + (inputs[6] + inputs[7]);

// Check if the total count is greater than or equal to 2
assign trigger = count >= 2;

endmodule
