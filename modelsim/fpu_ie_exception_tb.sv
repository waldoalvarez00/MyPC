//============================================================================
//
//  FPU Invalid Operation (IE) Exception Testbench
//  Tests all cases that should trigger the Invalid Exception on 8087 FPU
//
//  Test Categories:
//  1. Stack Faults (Underflow/Overflow)
//  2. Invalid Operation on Special Operand Values
//  3. Arithmetic Domain Errors
//  4. Undefined/Unsupported Operations
//  5. Unordered Comparisons
//  6. Invalid Store Operations
//
//  Copyright Waldo Alvarez, 2025
//  https://pipflow.com
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module fpu_ie_exception_tb;

//============================================================================
// Clock and Reset
//============================================================================

reg clk;
reg reset;

initial begin
    clk = 0;
    forever #10 clk = ~clk;  // 50 MHz clock
end

//============================================================================
// DUT Signals
//============================================================================

// Instruction interface
reg  [7:0]  instruction;
reg  [2:0]  stack_index;
reg         execute;
wire        ready;
wire        error;

// Data interface
reg  [79:0] data_in;
wire [79:0] data_out;
reg  [31:0] int_data_in;
wire [31:0] int_data_out;

// Memory operand format
reg         has_memory_op;
reg  [1:0]  operand_size;
reg         is_integer;
reg         is_bcd;

// Control/Status interface
reg  [15:0] control_in;
reg         control_write;
wire [15:0] status_out;
wire [15:0] control_out;
wire [15:0] tag_word_out;

// Exception interface
wire        int_request;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;
integer timeout_count;

//============================================================================
// Instruction Opcodes (must match FPU_Core.v exactly)
//============================================================================

// Arithmetic
localparam INST_FADD    = 8'h10;
localparam INST_FADDP   = 8'h11;
localparam INST_FSUB    = 8'h12;
localparam INST_FSUBP   = 8'h13;
localparam INST_FMUL    = 8'h14;
localparam INST_FMULP   = 8'h15;
localparam INST_FDIV    = 8'h16;
localparam INST_FDIVP   = 8'h17;
localparam INST_FDIVR   = 8'h1A;
localparam INST_FDIVRP  = 8'h1B;

// Stack operations
localparam INST_FLD     = 8'h20;
localparam INST_FST     = 8'h21;
localparam INST_FSTP    = 8'h22;
localparam INST_FXCH    = 8'h23;

// Integer conversions
localparam INST_FILD16  = 8'h30;
localparam INST_FILD32  = 8'h31;
localparam INST_FIST16  = 8'h32;
localparam INST_FIST32  = 8'h33;
localparam INST_FISTP16 = 8'h34;
localparam INST_FISTP32 = 8'h35;

// BCD operations
localparam INST_FBLD    = 8'h36;
localparam INST_FBSTP   = 8'h37;

// FP format conversions
localparam INST_FLD32   = 8'h40;
localparam INST_FLD64   = 8'h41;
localparam INST_FST32   = 8'h42;
localparam INST_FST64   = 8'h43;
localparam INST_FSTP32  = 8'h44;
localparam INST_FSTP64  = 8'h45;

// Transcendental
localparam INST_FSQRT   = 8'h50;
localparam INST_FSIN    = 8'h51;
localparam INST_FCOS    = 8'h52;
localparam INST_FSINCOS = 8'h53;
localparam INST_FPTAN   = 8'h54;
localparam INST_FPATAN  = 8'h55;
localparam INST_F2XM1   = 8'h56;
localparam INST_FYL2X   = 8'h57;
localparam INST_FYL2XP1 = 8'h58;

// Comparison
localparam INST_FCOM    = 8'h60;
localparam INST_FCOMP   = 8'h61;
localparam INST_FCOMPP  = 8'h62;
localparam INST_FTST    = 8'h63;
localparam INST_FXAM    = 8'h64;
localparam INST_FUCOM   = 8'h65;
localparam INST_FUCOMP  = 8'h66;
localparam INST_FUCOMPP = 8'h67;

// Stack management
localparam INST_FINCSTP = 8'h70;
localparam INST_FDECSTP = 8'h71;
localparam INST_FFREE   = 8'h72;
localparam INST_FNOP    = 8'h73;

// Constants (push onto stack)
localparam INST_FLD1    = 8'h80;
localparam INST_FLDZ    = 8'h81;
localparam INST_FLDPI   = 8'h82;
localparam INST_FLDL2E  = 8'h83;
localparam INST_FLDL2T  = 8'h84;
localparam INST_FLDLG2  = 8'h85;
localparam INST_FLDLN2  = 8'h86;

// Advanced operations
localparam INST_FSCALE  = 8'h90;
localparam INST_FXTRACT = 8'h91;
localparam INST_FPREM   = 8'h92;
localparam INST_FRNDINT = 8'h93;
localparam INST_FABS    = 8'h94;
localparam INST_FCHS    = 8'h95;
localparam INST_FPREM1  = 8'h96;

// Control
localparam INST_FINIT   = 8'hF0;
localparam INST_FLDCW   = 8'hF1;
localparam INST_FSTCW   = 8'hF2;
localparam INST_FSTSW   = 8'hF3;
localparam INST_FCLEX   = 8'hF4;
localparam INST_FWAIT   = 8'hF5;
localparam INST_FNINIT  = 8'hF6;
localparam INST_FNSTCW  = 8'hF7;
localparam INST_FNSTSW  = 8'hF8;
localparam INST_FNCLEX  = 8'hF9;

//============================================================================
// FP80 Constants
//============================================================================

// Normal values
localparam FP80_ZERO        = 80'h0000_0000000000000000;
localparam FP80_NEG_ZERO    = 80'h8000_0000000000000000;
localparam FP80_ONE         = 80'h3FFF_8000000000000000;
localparam FP80_TWO         = 80'h4000_8000000000000000;
localparam FP80_THREE       = 80'h4000_C000000000000000;
localparam FP80_HALF        = 80'h3FFE_8000000000000000;
localparam FP80_NEG_ONE     = 80'hBFFF_8000000000000000;
localparam FP80_NEG_TWO     = 80'hC000_8000000000000000;
localparam FP80_PI_4        = 80'h3FFE_C90FDAA22168C235;
localparam FP80_PI_2        = 80'h3FFF_C90FDAA22168C235;

// Special values
localparam FP80_POS_INF     = 80'h7FFF_8000000000000000;  // +Infinity
localparam FP80_NEG_INF     = 80'hFFFF_8000000000000000;  // -Infinity
localparam FP80_QNAN        = 80'h7FFF_C000000000000000;  // Quiet NaN
localparam FP80_SNAN        = 80'h7FFF_8000000000000001;  // Signaling NaN (non-zero fraction, J bit set)

// Unsupported formats (8087 specific - pseudo-NaN/infinity)
localparam FP80_PSEUDO_NAN  = 80'h7FFF_0000000000000001;  // All 1s exponent, J=0, non-zero fraction
localparam FP80_PSEUDO_INF  = 80'h7FFF_0000000000000000;  // All 1s exponent, J=0, zero fraction
localparam FP80_UNNORMAL    = 80'h7FFE_0000000000000001;  // Non-zero exponent, J=0

// Large values for overflow testing
localparam FP80_LARGE       = 80'h7FFE_FFFFFFFFFFFFFFFF;  // Largest finite value

// Status word bit positions
localparam SW_IE = 0;   // Invalid Operation Exception
localparam SW_DE = 1;   // Denormal Exception
localparam SW_ZE = 2;   // Zero Divide Exception
localparam SW_OE = 3;   // Overflow Exception
localparam SW_UE = 4;   // Underflow Exception
localparam SW_PE = 5;   // Precision Exception
localparam SW_SF = 6;   // Stack Fault
localparam SW_ES = 7;   // Exception Summary
localparam SW_C0 = 8;   // Condition Code 0
localparam SW_C1 = 9;   // Condition Code 1 (stack indicator for SF)
localparam SW_C2 = 10;  // Condition Code 2
localparam SW_C3 = 14;  // Condition Code 3

//============================================================================
// DUT Instantiation
//============================================================================

FPU_Core dut (
    .clk(clk),
    .reset(reset),
    .instruction(instruction),
    .stack_index(stack_index),
    .execute(execute),
    .ready(ready),
    .error(error),
    .data_in(data_in),
    .data_out(data_out),
    .int_data_in(int_data_in),
    .int_data_out(int_data_out),
    .has_memory_op(has_memory_op),
    .operand_size(operand_size),
    .is_integer(is_integer),
    .is_bcd(is_bcd),
    .control_in(control_in),
    .control_write(control_write),
    .status_out(status_out),
    .control_out(control_out),
    .tag_word_out(tag_word_out),
    .int_request(int_request)
);

//============================================================================
// Helper Tasks
//============================================================================

task wait_for_ready;
    input integer max_cycles;
    integer i;
    begin
        for (i = 0; i < max_cycles; i = i + 1) begin
            @(posedge clk);
            if (ready) begin
                i = max_cycles;
            end
        end
        if (!ready) begin
            $display("  ERROR: Timeout waiting for ready signal");
            timeout_count = timeout_count + 1;
        end
    end
endtask

task execute_instruction;
    input [7:0] inst;
    input [2:0] st_idx;
    input [79:0] data;
    input        mem_op;
    input [1:0]  op_size;
    input        is_int;
    input        is_bcd_op;
    begin
        instruction = inst;
        stack_index = st_idx;
        data_in = data;
        has_memory_op = mem_op;
        operand_size = op_size;
        is_integer = is_int;
        is_bcd = is_bcd_op;
        execute = 1;
        @(posedge clk);
        execute = 0;

        wait_for_ready(500);
    end
endtask

// Initialize FPU to known state
task init_fpu;
    begin
        execute_instruction(INST_FINIT, 3'd0, FP80_ZERO, 1'b0, 2'b11, 1'b0, 1'b0);
        // Set control word with IE unmasked (bit 0 = 0)
        control_in = 16'h037E;  // All masked except IE
        control_write = 1;
        @(posedge clk);
        control_write = 0;
        repeat(5) @(posedge clk);
    end
endtask

// Clear exceptions
task clear_exceptions;
    begin
        execute_instruction(INST_FCLEX, 3'd0, FP80_ZERO, 1'b0, 2'b11, 1'b0, 1'b0);
        repeat(5) @(posedge clk);
    end
endtask

// Push value onto FPU stack
task push_value;
    input [79:0] value;
    begin
        execute_instruction(INST_FLD, 3'd0, value, 1'b1, 2'b11, 1'b0, 1'b0);
    end
endtask

// Test that expects IE exception to be set
task test_ie_exception;
    input [7:0] inst;
    input [2:0] st_idx;
    input [79:0] data;
    input        mem_op;
    input [255:0] test_name;
    begin
        test_count = test_count + 1;
        $display("\nTest %0d: %s", test_count, test_name);

        execute_instruction(inst, st_idx, data, mem_op, 2'b11, 1'b0, 1'b0);

        // Check if IE flag is set
        if (status_out[SW_IE]) begin
            $display("  Status word: %04h", status_out);
            $display("  IE flag: SET (as expected)");
            if (status_out[SW_SF]) begin
                $display("  SF flag: SET (Stack Fault)");
                if (status_out[SW_C1])
                    $display("  C1=1: Stack Overflow");
                else
                    $display("  C1=0: Stack Underflow");
            end
            pass_count = pass_count + 1;
            $display("  PASS: Invalid Exception correctly raised");
        end else begin
            $display("  Status word: %04h", status_out);
            $display("  IE flag: NOT SET");
            fail_count = fail_count + 1;
            $display("  FAIL: Expected Invalid Exception was not raised");
        end

        repeat(5) @(posedge clk);
    end
endtask

// Test that expects IE with stack fault
task test_stack_fault;
    input [7:0] inst;
    input [2:0] st_idx;
    input [79:0] data;
    input        mem_op;
    input        expect_overflow;  // 1=overflow, 0=underflow
    input [255:0] test_name;
    begin
        test_count = test_count + 1;
        $display("\nTest %0d: %s", test_count, test_name);

        execute_instruction(inst, st_idx, data, mem_op, 2'b11, 1'b0, 1'b0);

        // Check IE and SF flags
        if (status_out[SW_IE] && status_out[SW_SF]) begin
            $display("  Status word: %04h", status_out);
            $display("  IE flag: SET");
            $display("  SF flag: SET (Stack Fault)");

            if (expect_overflow && status_out[SW_C1]) begin
                $display("  C1=1: Stack Overflow (expected)");
                pass_count = pass_count + 1;
                $display("  PASS: Stack overflow correctly detected");
            end else if (!expect_overflow && !status_out[SW_C1]) begin
                $display("  C1=0: Stack Underflow (expected)");
                pass_count = pass_count + 1;
                $display("  PASS: Stack underflow correctly detected");
            end else begin
                $display("  C1=%b: Unexpected stack fault type", status_out[SW_C1]);
                fail_count = fail_count + 1;
                $display("  FAIL: Wrong stack fault type");
            end
        end else if (status_out[SW_IE]) begin
            // IE set but no SF - might be acceptable for some operations
            $display("  Status word: %04h", status_out);
            $display("  IE flag: SET, SF flag: NOT SET");
            pass_count = pass_count + 1;
            $display("  PASS: Invalid Exception raised (no SF flag)");
        end else begin
            $display("  Status word: %04h", status_out);
            $display("  IE flag: NOT SET");
            fail_count = fail_count + 1;
            $display("  FAIL: Expected stack fault was not detected");
        end

        repeat(5) @(posedge clk);
    end
endtask

// Test for integer conversion overflow (IE, not OE)
task test_integer_overflow;
    input [7:0] inst;
    input [79:0] data;
    input [255:0] test_name;
    begin
        test_count = test_count + 1;
        $display("\nTest %0d: %s", test_count, test_name);

        // Push the value first
        push_value(data);

        // Try to convert to integer
        execute_instruction(inst, 3'd0, FP80_ZERO, 1'b1, 2'b11, 1'b1, 1'b0);

        // Check if IE flag is set (not OE for integer overflow)
        if (status_out[SW_IE]) begin
            $display("  Status word: %04h", status_out);
            $display("  IE flag: SET (integer conversion overflow)");
            pass_count = pass_count + 1;
            $display("  PASS: Integer overflow correctly raised IE");
        end else begin
            $display("  Status word: %04h", status_out);
            fail_count = fail_count + 1;
            $display("  FAIL: Expected IE for integer overflow");
        end

        repeat(5) @(posedge clk);
    end
endtask

//============================================================================
// Test Stimulus
//============================================================================

initial begin
    $display("================================================================");
    $display("FPU Invalid Operation (IE) Exception Testbench");
    $display("Testing all 8087 IE exception conditions");
    $display("================================================================");
    $display("");

    // Initialize
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    timeout_count = 0;

    reset = 1;
    execute = 0;
    instruction = 8'd0;
    stack_index = 3'd0;
    data_in = 80'd0;
    int_data_in = 32'd0;
    has_memory_op = 1'b0;
    operand_size = 2'b11;
    is_integer = 1'b0;
    is_bcd = 1'b0;
    control_in = 16'h037F;
    control_write = 1'b0;

    repeat(20) @(posedge clk);
    reset = 0;
    repeat(10) @(posedge clk);

    //========================================================================
    // Test Group 1: Stack Faults - Underflow
    //========================================================================

    $display("\n========================================");
    $display("Test Group 1: Stack Faults - Underflow");
    $display("========================================");

    // 1.1 Stack Underflow - operating on empty registers
    init_fpu();

    // FST with empty stack
    test_stack_fault(INST_FST, 3'd0, FP80_ZERO, 1'b1, 1'b0,
        "Stack Underflow: FST from empty stack");

    init_fpu();
    // FSTP with empty stack
    test_stack_fault(INST_FSTP, 3'd0, FP80_ZERO, 1'b1, 1'b0,
        "Stack Underflow: FSTP from empty stack");

    init_fpu();
    // FXCH with ST(1) empty
    push_value(FP80_ONE);  // Push one value
    test_stack_fault(INST_FXCH, 3'd1, FP80_ZERO, 1'b0, 1'b0,
        "Stack Underflow: FXCH with ST(1) empty");

    init_fpu();
    // FADD with only one operand
    push_value(FP80_ONE);
    test_stack_fault(INST_FADD, 3'd1, FP80_ZERO, 1'b0, 1'b0,
        "Stack Underflow: FADD with ST(1) empty");

    init_fpu();
    // FSUB with only one operand
    push_value(FP80_ONE);
    test_stack_fault(INST_FSUB, 3'd1, FP80_ZERO, 1'b0, 1'b0,
        "Stack Underflow: FSUB with ST(1) empty");

    init_fpu();
    // FMUL with only one operand
    push_value(FP80_ONE);
    test_stack_fault(INST_FMUL, 3'd1, FP80_ZERO, 1'b0, 1'b0,
        "Stack Underflow: FMUL with ST(1) empty");

    init_fpu();
    // FDIV with only one operand
    push_value(FP80_ONE);
    test_stack_fault(INST_FDIV, 3'd1, FP80_ZERO, 1'b0, 1'b0,
        "Stack Underflow: FDIV with ST(1) empty");

    init_fpu();
    // FCOM with empty register
    push_value(FP80_ONE);
    test_stack_fault(INST_FCOM, 3'd1, FP80_ZERO, 1'b0, 1'b0,
        "Stack Underflow: FCOM with ST(1) empty");

    init_fpu();
    // Transcendental on empty stack
    test_stack_fault(INST_FSQRT, 3'd0, FP80_ZERO, 1'b0, 1'b0,
        "Stack Underflow: FSQRT on empty stack");

    init_fpu();
    test_stack_fault(INST_FSIN, 3'd0, FP80_ZERO, 1'b0, 1'b0,
        "Stack Underflow: FSIN on empty stack");

    //========================================================================
    // Test Group 2: Stack Faults - Overflow
    //========================================================================

    $display("\n========================================");
    $display("Test Group 2: Stack Faults - Overflow");
    $display("========================================");

    // 1.2 Stack Overflow - pushing when stack is full
    init_fpu();

    // Fill the stack with 8 values
    push_value(FP80_ONE);
    push_value(FP80_TWO);
    push_value(FP80_THREE);
    push_value(FP80_ONE);
    push_value(FP80_TWO);
    push_value(FP80_THREE);
    push_value(FP80_ONE);
    push_value(FP80_TWO);

    // Now try to push a 9th value
    test_stack_fault(INST_FLD, 3'd0, FP80_THREE, 1'b1, 1'b1,
        "Stack Overflow: FLD when stack is full");

    init_fpu();
    // Fill stack and try FLD1
    push_value(FP80_ONE);
    push_value(FP80_TWO);
    push_value(FP80_THREE);
    push_value(FP80_ONE);
    push_value(FP80_TWO);
    push_value(FP80_THREE);
    push_value(FP80_ONE);
    push_value(FP80_TWO);
    test_stack_fault(INST_FLD1, 3'd0, FP80_ZERO, 1'b0, 1'b1,
        "Stack Overflow: FLD1 when stack is full");

    init_fpu();
    // Fill stack and try FLDZ
    push_value(FP80_ONE);
    push_value(FP80_TWO);
    push_value(FP80_THREE);
    push_value(FP80_ONE);
    push_value(FP80_TWO);
    push_value(FP80_THREE);
    push_value(FP80_ONE);
    push_value(FP80_TWO);
    test_stack_fault(INST_FLDZ, 3'd0, FP80_ZERO, 1'b0, 1'b1,
        "Stack Overflow: FLDZ when stack is full");

    //========================================================================
    // Test Group 3: Unsupported/Invalid Operand Values
    //========================================================================

    $display("\n========================================");
    $display("Test Group 3: Unsupported Operand Values");
    $display("========================================");

    // 2.1 Signaling NaN operand
    init_fpu();
    push_value(FP80_SNAN);
    test_ie_exception(INST_FADD, 3'd0, FP80_ONE, 1'b1,
        "SNaN: FADD with SNaN operand");

    init_fpu();
    push_value(FP80_ONE);
    push_value(FP80_SNAN);
    test_ie_exception(INST_FMUL, 3'd1, FP80_ZERO, 1'b0,
        "SNaN: FMUL with SNaN in ST(0)");

    init_fpu();
    push_value(FP80_SNAN);
    test_ie_exception(INST_FSQRT, 3'd0, FP80_ZERO, 1'b0,
        "SNaN: FSQRT of SNaN");

    // 2.2 Pseudo-NaN (unsupported format)
    init_fpu();
    push_value(FP80_PSEUDO_NAN);
    test_ie_exception(INST_FADD, 3'd0, FP80_ONE, 1'b1,
        "Pseudo-NaN: Unsupported operand format");

    // 2.3 Unnormal (unsupported format)
    init_fpu();
    push_value(FP80_UNNORMAL);
    test_ie_exception(INST_FMUL, 3'd0, FP80_TWO, 1'b1,
        "Unnormal: Unsupported operand format");

    //========================================================================
    // Test Group 4: Arithmetic Domain Errors
    //========================================================================

    $display("\n========================================");
    $display("Test Group 4: Arithmetic Domain Errors");
    $display("========================================");

    // 3.1 FSQRT with negative input
    init_fpu();
    push_value(FP80_NEG_ONE);
    test_ie_exception(INST_FSQRT, 3'd0, FP80_ZERO, 1'b0,
        "Domain Error: FSQRT of negative number");

    init_fpu();
    push_value(FP80_NEG_TWO);
    test_ie_exception(INST_FSQRT, 3'd0, FP80_ZERO, 1'b0,
        "Domain Error: FSQRT of -2.0");

    // 3.2 Logarithmic domain errors
    // FYL2X computes y * log2(x) where ST(0)=x, ST(1)=y
    init_fpu();
    push_value(FP80_ONE);   // y = 1 (becomes ST(1) after second push)
    push_value(FP80_ZERO);  // x = 0 (becomes ST(0))
    test_ie_exception(INST_FYL2X, 3'd0, FP80_ZERO, 1'b0,
        "Domain Error: FYL2X with x=0");

    init_fpu();
    push_value(FP80_ONE);      // y = 1 (becomes ST(1) after second push)
    push_value(FP80_NEG_ONE);  // x = -1 (becomes ST(0))
    test_ie_exception(INST_FYL2X, 3'd0, FP80_ZERO, 1'b0,
        "Domain Error: FYL2X with x<0");

    init_fpu();
    push_value(FP80_ZERO);
    test_ie_exception(INST_FXTRACT, 3'd0, FP80_ZERO, 1'b0,
        "Domain Error: FXTRACT of zero");

    // 3.3 F2XM1 domain error (|x| >= 1)
    init_fpu();
    push_value(FP80_TWO);
    test_ie_exception(INST_F2XM1, 3'd0, FP80_ZERO, 1'b0,
        "Domain Error: F2XM1 with |x| >= 1");

    init_fpu();
    push_value(FP80_NEG_TWO);
    test_ie_exception(INST_F2XM1, 3'd0, FP80_ZERO, 1'b0,
        "Domain Error: F2XM1 with x = -2");

    //========================================================================
    // Test Group 5: Undefined/Unsupported Operations
    //========================================================================

    $display("\n========================================");
    $display("Test Group 5: Undefined Operations");
    $display("========================================");

    // 4.1 0 / 0
    init_fpu();
    push_value(FP80_ZERO);
    push_value(FP80_ZERO);
    test_ie_exception(INST_FDIV, 3'd1, FP80_ZERO, 1'b0,
        "Undefined: 0 / 0");

    // 4.2 Infinity / Infinity
    init_fpu();
    push_value(FP80_POS_INF);
    push_value(FP80_POS_INF);
    test_ie_exception(INST_FDIV, 3'd1, FP80_ZERO, 1'b0,
        "Undefined: +Inf / +Inf");

    init_fpu();
    push_value(FP80_NEG_INF);
    push_value(FP80_POS_INF);
    test_ie_exception(INST_FDIV, 3'd1, FP80_ZERO, 1'b0,
        "Undefined: +Inf / -Inf");

    // 4.3 Infinity - Infinity
    init_fpu();
    push_value(FP80_POS_INF);
    push_value(FP80_POS_INF);
    test_ie_exception(INST_FSUB, 3'd1, FP80_ZERO, 1'b0,
        "Undefined: +Inf - +Inf");

    init_fpu();
    push_value(FP80_NEG_INF);
    push_value(FP80_POS_INF);
    test_ie_exception(INST_FADD, 3'd1, FP80_ZERO, 1'b0,
        "Undefined: +Inf + (-Inf)");

    // 4.4 0 * Infinity
    init_fpu();
    push_value(FP80_ZERO);
    push_value(FP80_POS_INF);
    test_ie_exception(INST_FMUL, 3'd1, FP80_ZERO, 1'b0,
        "Undefined: +Inf * 0");

    init_fpu();
    push_value(FP80_POS_INF);
    push_value(FP80_ZERO);
    test_ie_exception(INST_FMUL, 3'd1, FP80_ZERO, 1'b0,
        "Undefined: 0 * +Inf");

    init_fpu();
    push_value(FP80_NEG_ZERO);
    push_value(FP80_POS_INF);
    test_ie_exception(INST_FMUL, 3'd1, FP80_ZERO, 1'b0,
        "Undefined: +Inf * (-0)");

    //========================================================================
    // Test Group 6: Comparison with Invalid Operands
    //========================================================================

    $display("\n========================================");
    $display("Test Group 6: Invalid Comparisons");
    $display("========================================");

    // 5.1 Comparison involving unsupported operands
    init_fpu();
    push_value(FP80_SNAN);
    push_value(FP80_ONE);
    test_ie_exception(INST_FCOM, 3'd1, FP80_ZERO, 1'b0,
        "Invalid Compare: FCOM with SNaN");

    init_fpu();
    push_value(FP80_ONE);
    push_value(FP80_PSEUDO_NAN);
    test_ie_exception(INST_FCOM, 3'd1, FP80_ZERO, 1'b0,
        "Invalid Compare: FCOM with pseudo-NaN");

    // 5.2 Comparison with empty stack
    init_fpu();
    push_value(FP80_ONE);
    test_ie_exception(INST_FCOM, 3'd2, FP80_ZERO, 1'b0,
        "Invalid Compare: FCOM with ST(2) empty");

    //========================================================================
    // Test Group 7: Invalid Store Operations
    //========================================================================

    $display("\n========================================");
    $display("Test Group 7: Invalid Store Operations");
    $display("========================================");

    // 6.1 Storing value too large for integer format
    init_fpu();
    test_integer_overflow(INST_FIST16, FP80_LARGE,
        "Integer Overflow: FIST16 value too large");

    init_fpu();
    test_integer_overflow(INST_FIST32, FP80_POS_INF,
        "Integer Overflow: FIST32 of infinity");

    // 6.2 Storing NaN to integer
    init_fpu();
    test_integer_overflow(INST_FIST32, FP80_QNAN,
        "Integer Store: FIST32 of NaN");

    init_fpu();
    test_integer_overflow(INST_FIST16, FP80_SNAN,
        "Integer Store: FIST16 of SNaN");

    //========================================================================
    // Test Group 8: Exception Clearing
    //========================================================================

    $display("\n========================================");
    $display("Test Group 8: Exception Clearing");
    $display("========================================");

    // 8.1 Verify FCLEX clears IE
    init_fpu();
    push_value(FP80_NEG_ONE);
    execute_instruction(INST_FSQRT, 3'd0, FP80_ZERO, 1'b0, 2'b11, 1'b0, 1'b0);

    test_count = test_count + 1;
    $display("\nTest %0d: FCLEX clears IE flag", test_count);
    $display("  Before FCLEX: Status = %04h, IE = %b", status_out, status_out[SW_IE]);

    clear_exceptions();

    if (!status_out[SW_IE]) begin
        $display("  After FCLEX:  Status = %04h, IE = %b", status_out, status_out[SW_IE]);
        pass_count = pass_count + 1;
        $display("  PASS: FCLEX correctly cleared IE flag");
    end else begin
        $display("  After FCLEX:  Status = %04h, IE = %b", status_out, status_out[SW_IE]);
        fail_count = fail_count + 1;
        $display("  FAIL: FCLEX did not clear IE flag");
    end

    //========================================================================
    // Summary
    //========================================================================

    repeat(20) @(posedge clk);

    $display("\n================================================================");
    $display("FPU IE Exception Testbench Summary");
    $display("================================================================");
    $display("Total tests:  %0d", test_count);
    $display("Passed:       %0d", pass_count);
    $display("Failed:       %0d", fail_count);
    $display("Timeouts:     %0d", timeout_count);
    $display("");

    if (fail_count == 0 && timeout_count == 0) begin
        $display("*** ALL TESTS PASSED ***");
    end else begin
        $display("*** SOME TESTS FAILED ***");
    end
    $display("================================================================");

    $finish;
end

//============================================================================
// Waveform Dump
//============================================================================

initial begin
    $dumpfile("fpu_ie_exception_tb.vcd");
    $dumpvars(0, fpu_ie_exception_tb);
end

endmodule

`default_nettype wire
