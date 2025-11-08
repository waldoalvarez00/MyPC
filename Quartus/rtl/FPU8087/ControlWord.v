
module FPU_Control_Word_Register;

// Define the Control Word Register as a 16-bit register
reg [15:0] control_word;

// Aliases for different parts of the control word
wire [5:0] exception_masks = control_word[5:0]; // Exception Masking Bits (D5-D0)
wire interrupt_enable_mask = control_word[6];   // IEM Bit (Interrupt Enable/Mask)
wire infinity_control = control_word[7];        // IC Bit (Infinity Control)
wire [1:0] rounding_control = control_word[9:8];// RC Bits (Rounding Control)
wire [1:0] precision_control = control_word[11:10]; // PC Bits (Precision Control)
// Remaining bits can be unused or reserved for future use

// Initialize the control word register
initial begin
    control_word = 16'b0; // Set all bits to 0 initially
end

// Logic for updating the control word based on operations
// ...

endmodule