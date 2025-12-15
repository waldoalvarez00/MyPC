//============================================================================
//
//  FPU Exception Testbench (ZE, DE, OE, UE, PE)
//  Tests all numeric exception conditions on 8087 FPU
//
//  Test Categories:
//  1. ZE - Zero Divide Exception
//  2. DE - Denormalized Operand Exception
//  3. OE - Numeric Overflow Exception
//  4. UE - Numeric Underflow Exception
//  5. PE - Precision (Inexact Result) Exception
//
//  Copyright Waldo Alvarez, 2025
//  https://pipflow.com
//
//============================================================================

`timescale 1ns/1ps
`default_nettype none

module fpu_exceptions_tb;

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
// Instruction Opcodes
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
localparam INST_FSUBR   = 8'h18;
localparam INST_FDIVR   = 8'h19;

// Stack operations
localparam INST_FLD     = 8'h20;
localparam INST_FST     = 8'h21;
localparam INST_FSTP    = 8'h22;
localparam INST_FXCH    = 8'h23;
localparam INST_FFREE   = 8'h24;

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
localparam INST_FXTRACT = 8'h59;

// Comparison
localparam INST_FCOM    = 8'h60;
localparam INST_FCOMP   = 8'h61;
localparam INST_FCOMPP  = 8'h62;
localparam INST_FTST    = 8'h63;
localparam INST_FXAM    = 8'h64;
localparam INST_FUCOM   = 8'h65;
localparam INST_FUCOMP  = 8'h66;

// Miscellaneous
localparam INST_FABS    = 8'h70;
localparam INST_FCHS    = 8'h71;
localparam INST_FRNDINT = 8'h72;
localparam INST_FSCALE  = 8'h73;
localparam INST_FPREM   = 8'h74;
localparam INST_FLD1    = 8'h75;
localparam INST_FLDZ    = 8'h76;
localparam INST_FLDPI   = 8'h77;
localparam INST_FLDL2E  = 8'h78;
localparam INST_FLDL2T  = 8'h79;
localparam INST_FLDLG2  = 8'h7A;
localparam INST_FLDLN2  = 8'h7B;

// Control
localparam INST_FINIT   = 8'hF0;
localparam INST_FLDCW   = 8'hF1;
localparam INST_FSTCW   = 8'hF2;
localparam INST_FSTSW   = 8'hF3;
localparam INST_FCLEX   = 8'hF4;
localparam INST_FWAIT   = 8'hF5;
localparam INST_FDECSTP = 8'hF6;
localparam INST_FINCSTP = 8'hF7;

//============================================================================
// FP80 Constants
//============================================================================

// Normal values
localparam FP80_ZERO        = 80'h0000_0000000000000000;
localparam FP80_NEG_ZERO    = 80'h8000_0000000000000000;
localparam FP80_ONE         = 80'h3FFF_8000000000000000;
localparam FP80_TWO         = 80'h4000_8000000000000000;
localparam FP80_THREE       = 80'h4000_C000000000000000;
localparam FP80_FOUR        = 80'h4001_8000000000000000;
localparam FP80_TEN         = 80'h4002_A000000000000000;
localparam FP80_HALF        = 80'h3FFE_8000000000000000;
localparam FP80_THIRD       = 80'h3FFD_AAAAAAAAAAAAAAAB;  // 1/3 (inexact)
localparam FP80_NEG_ONE     = 80'hBFFF_8000000000000000;
localparam FP80_NEG_TWO     = 80'hC000_8000000000000000;
localparam FP80_PI_4        = 80'h3FFE_C90FDAA22168C235;
localparam FP80_PI_2        = 80'h3FFF_C90FDAA22168C235;

// Special values
localparam FP80_POS_INF     = 80'h7FFF_8000000000000000;  // +Infinity
localparam FP80_NEG_INF     = 80'hFFFF_8000000000000000;  // -Infinity
localparam FP80_QNAN        = 80'h7FFF_C000000000000000;  // Quiet NaN
localparam FP80_SNAN        = 80'h7FFF_8000000000000001;  // Signaling NaN

// Very large values for overflow testing
// Max exponent = 0x7FFE (before infinity), max mantissa
localparam FP80_LARGE       = 80'h7FFE_FFFFFFFFFFFFFFFF;  // Largest finite positive
localparam FP80_NEG_LARGE   = 80'hFFFE_FFFFFFFFFFFFFFFF;  // Largest finite negative
localparam FP80_HALF_MAX    = 80'h7FFD_FFFFFFFFFFFFFFFF;  // Half of max

// Very small values for underflow testing
// Min exponent = 0x0001 (before denormal), min mantissa with J bit
localparam FP80_TINY        = 80'h0001_8000000000000000;  // Smallest positive normal
localparam FP80_NEG_TINY    = 80'h8001_8000000000000000;  // Smallest negative normal
localparam FP80_SMALL       = 80'h0010_8000000000000000;  // Small positive normal

// Denormalized values (exponent = 0, J bit = 0)
localparam FP80_DENORM_POS  = 80'h0000_4000000000000000;  // Positive denormal
localparam FP80_DENORM_NEG  = 80'h8000_4000000000000000;  // Negative denormal
localparam FP80_DENORM_TINY = 80'h0000_0000000000000001;  // Smallest denormal

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
localparam SW_C1 = 9;   // Condition Code 1
localparam SW_C2 = 10;  // Condition Code 2
localparam SW_C3 = 14;  // Condition Code 3

// Control word mask positions (0 = unmasked, 1 = masked)
localparam CW_IM = 0;   // Invalid Operation Mask
localparam CW_DM = 1;   // Denormal Mask
localparam CW_ZM = 2;   // Zero Divide Mask
localparam CW_OM = 3;   // Overflow Mask
localparam CW_UM = 4;   // Underflow Mask
localparam CW_PM = 5;   // Precision Mask

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

// Initialize FPU to known state with all exceptions masked
task init_fpu;
    begin
        execute_instruction(INST_FINIT, 3'd0, FP80_ZERO, 1'b0, 2'b11, 1'b0, 1'b0);
        // Default: all exceptions masked (0x037F)
        control_in = 16'h037F;
        control_write = 1;
        @(posedge clk);
        control_write = 0;
        repeat(5) @(posedge clk);
    end
endtask

// Initialize FPU with specific exception unmasked
task init_fpu_unmask;
    input integer exception_bit;
    begin
        execute_instruction(INST_FINIT, 3'd0, FP80_ZERO, 1'b0, 2'b11, 1'b0, 1'b0);
        // Unmask the specified exception
        control_in = 16'h037F & ~(1 << exception_bit);
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

// Generic exception test task
task test_exception;
    input integer exc_bit;
    input [255:0] exc_name;
    input [7:0] inst;
    input [2:0] st_idx;
    input [79:0] data;
    input        mem_op;
    input [255:0] test_name;
    begin
        test_count = test_count + 1;
        $display("\nTest %0d: %s", test_count, test_name);

        execute_instruction(inst, st_idx, data, mem_op, 2'b11, 1'b0, 1'b0);

        // Check if the specific exception flag is set
        if (status_out[exc_bit]) begin
            $display("  Status word: %04h", status_out);
            $display("  %s flag: SET (as expected)", exc_name);
            pass_count = pass_count + 1;
            $display("  PASS: %s correctly raised", exc_name);
        end else begin
            $display("  Status word: %04h", status_out);
            $display("  %s flag: NOT SET", exc_name);
            fail_count = fail_count + 1;
            $display("  FAIL: Expected %s was not raised", exc_name);
        end

        repeat(5) @(posedge clk);
    end
endtask

// Test for ZE (Zero Divide) exception
task test_ze_exception;
    input [7:0] inst;
    input [2:0] st_idx;
    input [79:0] data;
    input        mem_op;
    input [255:0] test_name;
    begin
        test_exception(SW_ZE, "ZE", inst, st_idx, data, mem_op, test_name);
    end
endtask

// Test for DE (Denormal) exception
task test_de_exception;
    input [7:0] inst;
    input [2:0] st_idx;
    input [79:0] data;
    input        mem_op;
    input [255:0] test_name;
    begin
        test_exception(SW_DE, "DE", inst, st_idx, data, mem_op, test_name);
    end
endtask

// Test for OE (Overflow) exception
task test_oe_exception;
    input [7:0] inst;
    input [2:0] st_idx;
    input [79:0] data;
    input        mem_op;
    input [255:0] test_name;
    begin
        test_exception(SW_OE, "OE", inst, st_idx, data, mem_op, test_name);
    end
endtask

// Test for UE (Underflow) exception
task test_ue_exception;
    input [7:0] inst;
    input [2:0] st_idx;
    input [79:0] data;
    input        mem_op;
    input [255:0] test_name;
    begin
        test_exception(SW_UE, "UE", inst, st_idx, data, mem_op, test_name);
    end
endtask

// Test for PE (Precision) exception
task test_pe_exception;
    input [7:0] inst;
    input [2:0] st_idx;
    input [79:0] data;
    input        mem_op;
    input [255:0] test_name;
    begin
        test_exception(SW_PE, "PE", inst, st_idx, data, mem_op, test_name);
    end
endtask

// Test that exception is cleared by FCLEX
task test_exception_clear;
    input integer exc_bit;
    input [255:0] exc_name;
    begin
        test_count = test_count + 1;
        $display("\nTest %0d: FCLEX clears %s flag", test_count, exc_name);
        $display("  Before FCLEX: Status = %04h, %s = %b", status_out, exc_name, status_out[exc_bit]);

        clear_exceptions();

        if (!status_out[exc_bit]) begin
            $display("  After FCLEX:  Status = %04h, %s = %b", status_out, exc_name, status_out[exc_bit]);
            pass_count = pass_count + 1;
            $display("  PASS: FCLEX correctly cleared %s flag", exc_name);
        end else begin
            $display("  After FCLEX:  Status = %04h, %s = %b", status_out, exc_name, status_out[exc_bit]);
            fail_count = fail_count + 1;
            $display("  FAIL: FCLEX did not clear %s flag", exc_name);
        end
    end
endtask

//============================================================================
// Test Stimulus
//============================================================================

initial begin
    $display("================================================================");
    $display("FPU Exception Testbench (ZE, DE, OE, UE, PE)");
    $display("Testing all 8087 numeric exception conditions");
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
    // Test Group 1: ZE - Zero Divide Exception
    //========================================================================

    $display("\n========================================");
    $display("Test Group 1: ZE - Zero Divide Exception");
    $display("========================================");

    // 1.1 FDIV with divisor = 0 (non-zero numerator)
    // FDIV ST(i) computes: ST(0) = ST(0) / ST(i)
    // For 1/0, need ST(0)=1, ST(1)=0
    init_fpu();
    push_value(FP80_ZERO);          // divisor = 0 (becomes ST(1))
    push_value(FP80_ONE);           // numerator = 1 (becomes ST(0))
    test_ze_exception(INST_FDIV, 3'd1, FP80_ZERO, 1'b0,
        "ZE: FDIV 1.0 / 0.0");

    init_fpu();
    push_value(FP80_ZERO);          // divisor = 0 (becomes ST(1))
    push_value(FP80_TWO);           // numerator = 2 (becomes ST(0))
    test_ze_exception(INST_FDIV, 3'd1, FP80_ZERO, 1'b0,
        "ZE: FDIV 2.0 / 0.0");

    init_fpu();
    push_value(FP80_ZERO);          // divisor = 0 (becomes ST(1))
    push_value(FP80_NEG_ONE);       // numerator = -1 (becomes ST(0))
    test_ze_exception(INST_FDIV, 3'd1, FP80_ZERO, 1'b0,
        "ZE: FDIV -1.0 / 0.0");

    init_fpu();
    push_value(FP80_NEG_ZERO);      // divisor = -0 (becomes ST(1))
    push_value(FP80_TEN);           // numerator = 10 (becomes ST(0))
    test_ze_exception(INST_FDIV, 3'd1, FP80_ZERO, 1'b0,
        "ZE: FDIV 10.0 / -0.0");

    // 1.2 FDIVR with divisor = 0
    // FDIVR ST(i) computes: ST(0) = ST(i) / ST(0)
    // For 1/0, need ST(1)=1, ST(0)=0
    init_fpu();
    push_value(FP80_ONE);           // numerator = 1 (becomes ST(1))
    push_value(FP80_ZERO);          // divisor = 0 (becomes ST(0))
    test_ze_exception(INST_FDIVR, 3'd1, FP80_ZERO, 1'b0,
        "ZE: FDIVR (reversed) 1.0 / 0.0");

    // 1.3 Verify ZE flag can be cleared
    test_exception_clear(SW_ZE, "ZE");

    //========================================================================
    // Test Group 2: DE - Denormalized Operand Exception
    //========================================================================

    $display("\n========================================");
    $display("Test Group 2: DE - Denormalized Operand");
    $display("========================================");

    // 2.1 FADD with denormal operand
    init_fpu();
    push_value(FP80_DENORM_POS);    // Denormal value
    test_de_exception(INST_FADD, 3'd0, FP80_ONE, 1'b1,
        "DE: FADD denormal + 1.0");

    init_fpu();
    push_value(FP80_ONE);
    push_value(FP80_DENORM_POS);
    test_de_exception(INST_FADD, 3'd1, FP80_ZERO, 1'b0,
        "DE: FADD 1.0 + denormal (stack)");

    // 2.2 FSUB with denormal operand
    init_fpu();
    push_value(FP80_DENORM_NEG);
    test_de_exception(INST_FSUB, 3'd0, FP80_ONE, 1'b1,
        "DE: FSUB denormal - 1.0");

    // 2.3 FMUL with denormal operand
    init_fpu();
    push_value(FP80_DENORM_POS);
    test_de_exception(INST_FMUL, 3'd0, FP80_TWO, 1'b1,
        "DE: FMUL denormal * 2.0");

    init_fpu();
    push_value(FP80_TEN);
    push_value(FP80_DENORM_POS);
    test_de_exception(INST_FMUL, 3'd1, FP80_ZERO, 1'b0,
        "DE: FMUL 10.0 * denormal");

    // 2.4 FDIV with denormal operand
    init_fpu();
    push_value(FP80_DENORM_POS);
    test_de_exception(INST_FDIV, 3'd0, FP80_ONE, 1'b1,
        "DE: FDIV denormal / 1.0");

    init_fpu();
    push_value(FP80_ONE);
    push_value(FP80_DENORM_POS);
    test_de_exception(INST_FDIV, 3'd1, FP80_ZERO, 1'b0,
        "DE: FDIV 1.0 / denormal");

    // 2.5 FSQRT of denormal - SKIPPED (SQRT is microcode-only, not hardware testable)
    // init_fpu();
    // push_value(FP80_DENORM_POS);
    // test_de_exception(INST_FSQRT, 3'd0, FP80_ZERO, 1'b0,
    //     "DE: FSQRT of denormal");

    // 2.6 FCOM with denormal
    init_fpu();
    push_value(FP80_ONE);
    push_value(FP80_DENORM_POS);
    test_de_exception(INST_FCOM, 3'd1, FP80_ZERO, 1'b0,
        "DE: FCOM 1.0 vs denormal");

    // 2.7 Transcendental with denormal (should produce DE)
    init_fpu();
    push_value(FP80_DENORM_POS);
    test_de_exception(INST_FSIN, 3'd0, FP80_ZERO, 1'b0,
        "DE: FSIN of denormal");

    // 2.8 Verify DE flag can be cleared
    test_exception_clear(SW_DE, "DE");

    //========================================================================
    // Test Group 3: OE - Numeric Overflow Exception
    //========================================================================

    $display("\n========================================");
    $display("Test Group 3: OE - Numeric Overflow");
    $display("========================================");

    // 3.1 FMUL LARGE * LARGE (overflow)
    init_fpu();
    push_value(FP80_LARGE);
    push_value(FP80_LARGE);
    test_oe_exception(INST_FMUL, 3'd1, FP80_ZERO, 1'b0,
        "OE: FMUL LARGE * LARGE");

    // 3.2 FADD LARGE + LARGE (overflow)
    init_fpu();
    push_value(FP80_LARGE);
    push_value(FP80_LARGE);
    test_oe_exception(INST_FADD, 3'd1, FP80_ZERO, 1'b0,
        "OE: FADD LARGE + LARGE");

    // 3.3 Verify OE flag can be cleared
    test_exception_clear(SW_OE, "OE");

    //========================================================================
    // Test Group 4: UE - Numeric Underflow Exception
    //========================================================================

    $display("\n========================================");
    $display("Test Group 4: UE - Numeric Underflow");
    $display("========================================");

    // 4.1 FMUL TINY * TINY (underflow)
    init_fpu();
    push_value(FP80_TINY);
    push_value(FP80_TINY);
    test_ue_exception(INST_FMUL, 3'd1, FP80_ZERO, 1'b0,
        "UE: FMUL TINY * TINY");

    // 4.2 Verify UE flag can be cleared
    test_exception_clear(SW_UE, "UE");

    //========================================================================
    // Test Group 5: PE - Precision Exception
    //========================================================================

    $display("\n========================================");
    $display("Test Group 5: PE - Precision Exception");
    $display("========================================");

    // 5.1 FDIV with inexact result (1/3)
    init_fpu();
    push_value(FP80_THREE); // divisor (becomes ST(1))
    push_value(FP80_ONE);   // numerator (becomes ST(0))
    test_pe_exception(INST_FDIV, 3'd1, FP80_ZERO, 1'b0,
        "PE: FDIV 1.0 / 3.0 (inexact)");

    // 5.2 FSQRT with inexact result - SKIPPED (SQRT is microcode-only, not hardware testable)
    // init_fpu();
    // push_value(FP80_TWO);
    // test_pe_exception(INST_FSQRT, 3'd0, FP80_ZERO, 1'b0,
    //     "PE: FSQRT(2) (irrational)");

    // 5.3 Verify PE flag can be cleared
    test_exception_clear(SW_PE, "PE");

    //========================================================================
    // Test Group 6: Exception Stickiness
    //========================================================================

    $display("\n========================================");
    $display("Test Group 6: Exception Stickiness");
    $display("========================================");

    // 6.1 Multiple exceptions should OR together
    init_fpu();

    // First trigger ZE (1.0 / 0.0)
    push_value(FP80_ZERO);  // ST(1) = 0
    push_value(FP80_ONE);   // ST(0) = 1
    execute_instruction(INST_FDIV, 3'd1, FP80_ZERO, 1'b0, 2'b11, 1'b0, 1'b0);
    $display("  After FDIV: Status = %04h, ZE = %b, DE = %b", status_out, status_out[SW_ZE], status_out[SW_DE]);

    test_count = test_count + 1;
    $display("\nTest %0d: Exception flags are sticky", test_count);

    // Now trigger DE (don't clear first) - operation with denormal
    push_value(FP80_ONE);
    $display("  After push_value(ONE): Status = %04h, ZE = %b", status_out, status_out[SW_ZE]);
    push_value(FP80_DENORM_POS);
    $display("  After push_value(DENORM): Status = %04h, ZE = %b", status_out, status_out[SW_ZE]);
    execute_instruction(INST_FADD, 3'd1, FP80_ZERO, 1'b0, 2'b11, 1'b0, 1'b0);
    $display("  After FADD: Status = %04h, ZE = %b, DE = %b", status_out, status_out[SW_ZE], status_out[SW_DE]);

    // Both ZE and DE should be set
    if (status_out[SW_ZE] && status_out[SW_DE]) begin
        $display("  Status word: %04h", status_out);
        $display("  ZE = %b, DE = %b (both set)", status_out[SW_ZE], status_out[SW_DE]);
        pass_count = pass_count + 1;
        $display("  PASS: Exception flags are sticky");
    end else begin
        $display("  Status word: %04h", status_out);
        $display("  ZE = %b, DE = %b", status_out[SW_ZE], status_out[SW_DE]);
        fail_count = fail_count + 1;
        $display("  FAIL: Exception flags should be sticky");
    end

    // 6.2 FCLEX clears all exception flags
    test_count = test_count + 1;
    $display("\nTest %0d: FCLEX clears all exception flags", test_count);

    clear_exceptions();

    if (!(status_out[SW_ZE] || status_out[SW_PE] || status_out[SW_OE] ||
          status_out[SW_UE] || status_out[SW_DE])) begin
        $display("  Status word: %04h", status_out);
        pass_count = pass_count + 1;
        $display("  PASS: FCLEX cleared all exception flags");
    end else begin
        $display("  Status word: %04h", status_out);
        fail_count = fail_count + 1;
        $display("  FAIL: FCLEX did not clear all flags");
    end

    //========================================================================
    // Test Group 7: Exact Operations (No PE)
    //========================================================================

    $display("\n========================================");
    $display("Test Group 7: Exact Operations (No PE)");
    $display("========================================");

    // Operations that should NOT produce PE

    // 7.1 Exact division
    init_fpu();
    push_value(FP80_ONE);
    push_value(FP80_TWO);
    execute_instruction(INST_FDIV, 3'd1, FP80_ZERO, 1'b0, 2'b11, 1'b0, 1'b0);

    test_count = test_count + 1;
    $display("\nTest %0d: FDIV 1.0 / 2.0 (exact)", test_count);
    if (!status_out[SW_PE]) begin
        $display("  Status word: %04h, PE = 0 (as expected)", status_out);
        pass_count = pass_count + 1;
        $display("  PASS: Exact division does not set PE");
    end else begin
        $display("  Status word: %04h, PE = %b", status_out, status_out[SW_PE]);
        fail_count = fail_count + 1;
        $display("  FAIL: Exact division should not set PE");
    end

    // 7.2 Exact square root - SKIPPED (SQRT is microcode-only, not hardware testable)
    // init_fpu();
    // push_value(FP80_FOUR);
    // execute_instruction(INST_FSQRT, 3'd0, FP80_ZERO, 1'b0, 2'b11, 1'b0, 1'b0);
    //
    // test_count = test_count + 1;
    // $display("\nTest %0d: FSQRT(4) = 2.0 (exact)", test_count);
    // if (!status_out[SW_PE]) begin
    //     $display("  Status word: %04h, PE = 0 (as expected)", status_out);
    //     pass_count = pass_count + 1;
    //     $display("  PASS: Exact square root does not set PE");
    // end else begin
    //     $display("  Status word: %04h, PE = %b", status_out, status_out[SW_PE]);
    //     fail_count = fail_count + 1;
    //     $display("  FAIL: Exact square root should not set PE");
    // end

    // 7.3 Exact addition
    init_fpu();
    push_value(FP80_ONE);
    push_value(FP80_ONE);
    execute_instruction(INST_FADD, 3'd1, FP80_ZERO, 1'b0, 2'b11, 1'b0, 1'b0);

    test_count = test_count + 1;
    $display("\nTest %0d: FADD 1.0 + 1.0 = 2.0 (exact)", test_count);
    if (!status_out[SW_PE]) begin
        $display("  Status word: %04h, PE = 0 (as expected)", status_out);
        pass_count = pass_count + 1;
        $display("  PASS: Exact addition does not set PE");
    end else begin
        $display("  Status word: %04h, PE = %b", status_out, status_out[SW_PE]);
        fail_count = fail_count + 1;
        $display("  FAIL: Exact addition should not set PE");
    end

    //========================================================================
    // Summary
    //========================================================================

    repeat(20) @(posedge clk);

    $display("\n================================================================");
    $display("FPU Exception Testbench Summary");
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
    $dumpfile("fpu_exceptions_tb.vcd");
    $dumpvars(0, fpu_exceptions_tb);
end

endmodule

`default_nettype wire
