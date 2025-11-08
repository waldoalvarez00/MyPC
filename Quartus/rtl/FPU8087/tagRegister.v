module FPU_Tag_Register;

// Define the Tag Register as a 16-bit register
reg [15:0] tag_register;

// Aliases for each tag pair (2 bits per stack register)
wire [1:0] tag_ST0 = tag_register[1:0];   // Tag for ST(0)
wire [1:0] tag_ST1 = tag_register[3:2];   // Tag for ST(1)
wire [1:0] tag_ST2 = tag_register[5:4];   // Tag for ST(2)
wire [1:0] tag_ST3 = tag_register[7:6];   // Tag for ST(3)
wire [1:0] tag_ST4 = tag_register[9:8];   // Tag for ST(4)
wire [1:0] tag_ST5 = tag_register[11:10]; // Tag for ST(5)
wire [1:0] tag_ST6 = tag_register[13:12]; // Tag for ST(6)
wire [1:0] tag_ST7 = tag_register[15:14]; // Tag for ST(7)

// Initialize the tag register
initial begin
    tag_register = 16'hFFFF; // Assuming all stack registers are initially empty
end

// Logic for updating the tag register based on operations on the stack
// ...

endmodule
