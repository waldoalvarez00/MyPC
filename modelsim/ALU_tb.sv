`timescale 1ns/1ps

// Include necessary type definitions
`include "../Quartus/rtl/CPU/FlagsEnum.sv"
`include "../Quartus/rtl/CPU/MicrocodeTypes.sv"

module ALU_tb;

// Testbench signals
logic [15:0] a;
logic [15:0] b;
logic [31:0] out;
logic is_8_bit;
logic [5:0] op;  // MC_ALUOp_t
logic [15:0] flags_in;
logic [15:0] flags_out;
logic multibit_shift;
logic [4:0] shift_count;
logic busy;

// Test statistics
integer test_count = 0;
integer pass_count = 0;
integer fail_count = 0;

// Instantiate the ALU (tasks are included at compile time)
ALU uut (
    .a(a),
    .b(b),
    .out(out),
    .is_8_bit(is_8_bit),
    .op(op),
    .flags_in(flags_in),
    .flags_out(flags_out),
    .multibit_shift(multibit_shift),
    .shift_count(shift_count),
    .busy(busy)
);

// Test task for arithmetic operations
task automatic check_alu(input string test_name, input logic [31:0] expected_out,
                         input logic [15:0] expected_flags);
    #1;  // Wait for combinational logic
    test_count++;
    if (out === expected_out && (expected_flags === 16'hxxxx || flags_out === expected_flags)) begin
        $display("[PASS] %s: out=0x%08h, flags=0x%04h", test_name, out, flags_out);
        pass_count++;
    end else begin
        $display("[FAIL] %s:", test_name);
        $display("       Expected: out=0x%08h, flags=0x%04h", expected_out, expected_flags);
        $display("       Got:      out=0x%08h, flags=0x%04h", out, flags_out);
        fail_count++;
    end
endtask

// Test task for operations where we only check result, not flags
task automatic check_result(input string test_name, input logic [31:0] expected_out);
    #1;
    test_count++;
    if (out === expected_out) begin
        $display("[PASS] %s: out=0x%08h", test_name, out);
        pass_count++;
    end else begin
        $display("[FAIL] %s: Expected 0x%08h, Got 0x%08h", test_name, expected_out, out);
        fail_count++;
    end
endtask

// Main test sequence
initial begin
    $display("========================================");
    $display("ALU Testbench Started");
    $display("========================================");

    // Initialize signals
    a = 16'h0000;
    b = 16'h0000;
    is_8_bit = 0;
    op = 6'd0;
    flags_in = 16'h0000;
    multibit_shift = 0;
    shift_count = 5'd0;
    #10;

    //========================================
    // TEST 1: SELECT Operations
    //========================================
    $display("\n--- TEST 1: SELECT Operations ---");

    a = 16'h1234;
    b = 16'h5678;
    op = 6'd0;  // ALUOp_SELA
    check_result("SELA", 32'h00001234);

    op = 6'd1;  // ALUOp_SELB
    check_result("SELB", 32'h00005678);

    //========================================
    // TEST 2: 16-bit ADD Operations
    //========================================
    $display("\n--- TEST 2: 16-bit ADD Operations ---");
    is_8_bit = 0;
    flags_in = 16'h0000;

    // Simple addition without overflow
    a = 16'h0100;
    b = 16'h0200;
    op = 6'd2;  // ALUOp_ADD
    #1;
    if (out[15:0] == 16'h0300 && flags_out[CF_IDX] == 0 && flags_out[OF_IDX] == 0 &&
        flags_out[ZF_IDX] == 0 && flags_out[SF_IDX] == 0) begin
        $display("[PASS] ADD 0x0100 + 0x0200 = 0x0300");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] ADD 0x0100 + 0x0200: out=0x%04h, CF=%b, OF=%b, ZF=%b, SF=%b",
                 out[15:0], flags_out[CF_IDX], flags_out[OF_IDX],
                 flags_out[ZF_IDX], flags_out[SF_IDX]);
        fail_count++;
        test_count++;
    end

    // Addition with carry
    a = 16'hFFFF;
    b = 16'h0001;
    op = 6'd2;  // ALUOp_ADD
    #1;
    if (out[15:0] == 16'h0000 && flags_out[CF_IDX] == 1 && flags_out[ZF_IDX] == 1) begin
        $display("[PASS] ADD 0xFFFF + 0x0001 = 0x0000 with CF=1, ZF=1");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] ADD with carry: out=0x%04h, CF=%b, ZF=%b",
                 out[15:0], flags_out[CF_IDX], flags_out[ZF_IDX]);
        fail_count++;
        test_count++;
    end

    // Addition with overflow (positive + positive = negative)
    a = 16'h7FFF;
    b = 16'h0001;
    op = 6'd2;  // ALUOp_ADD
    #1;
    if (out[15:0] == 16'h8000 && flags_out[OF_IDX] == 1 && flags_out[SF_IDX] == 1) begin
        $display("[PASS] ADD 0x7FFF + 0x0001 = 0x8000 with OF=1, SF=1");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] ADD with overflow: out=0x%04h, OF=%b, SF=%b",
                 out[15:0], flags_out[OF_IDX], flags_out[SF_IDX]);
        fail_count++;
        test_count++;
    end

    //========================================
    // TEST 3: 8-bit ADD Operations
    //========================================
    $display("\n--- TEST 3: 8-bit ADD Operations ---");
    is_8_bit = 1;
    flags_in = 16'h0000;

    a = 16'h0050;
    b = 16'h0030;
    op = 6'd2;  // ALUOp_ADD
    #1;
    if (out[7:0] == 8'h80 && flags_out[SF_IDX] == 1 && flags_out[ZF_IDX] == 0) begin
        $display("[PASS] ADD8 0x50 + 0x30 = 0x80 with SF=1");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] ADD8: out=0x%02h, SF=%b, ZF=%b",
                 out[7:0], flags_out[SF_IDX], flags_out[ZF_IDX]);
        fail_count++;
        test_count++;
    end

    a = 16'h00FF;
    b = 16'h0001;
    op = 6'd2;  // ALUOp_ADD
    #1;
    if (out[7:0] == 8'h00 && flags_out[CF_IDX] == 1 && flags_out[ZF_IDX] == 1) begin
        $display("[PASS] ADD8 0xFF + 0x01 = 0x00 with CF=1, ZF=1");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] ADD8 with carry: out=0x%02h, CF=%b, ZF=%b",
                 out[7:0], flags_out[CF_IDX], flags_out[ZF_IDX]);
        fail_count++;
        test_count++;
    end

    //========================================
    // TEST 4: 16-bit SUB Operations
    //========================================
    $display("\n--- TEST 4: 16-bit SUB Operations ---");
    is_8_bit = 0;
    flags_in = 16'h0000;

    a = 16'h0300;
    b = 16'h0200;
    op = 6'd7;  // ALUOp_SUB
    #1;
    if (out[15:0] == 16'h0100 && flags_out[CF_IDX] == 0 && flags_out[ZF_IDX] == 0) begin
        $display("[PASS] SUB 0x0300 - 0x0200 = 0x0100");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] SUB: out=0x%04h, CF=%b, ZF=%b",
                 out[15:0], flags_out[CF_IDX], flags_out[ZF_IDX]);
        fail_count++;
        test_count++;
    end

    // Subtraction with borrow
    a = 16'h0000;
    b = 16'h0001;
    op = 6'd7;  // ALUOp_SUB
    #1;
    if (out[15:0] == 16'hFFFF && flags_out[CF_IDX] == 1 && flags_out[SF_IDX] == 1) begin
        $display("[PASS] SUB 0x0000 - 0x0001 = 0xFFFF with CF=1, SF=1");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] SUB with borrow: out=0x%04h, CF=%b, SF=%b",
                 out[15:0], flags_out[CF_IDX], flags_out[SF_IDX]);
        fail_count++;
        test_count++;
    end

    // Zero result
    a = 16'h1234;
    b = 16'h1234;
    op = 6'd7;  // ALUOp_SUB
    #1;
    if (out[15:0] == 16'h0000 && flags_out[ZF_IDX] == 1) begin
        $display("[PASS] SUB 0x1234 - 0x1234 = 0x0000 with ZF=1");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] SUB zero result: out=0x%04h, ZF=%b",
                 out[15:0], flags_out[ZF_IDX]);
        fail_count++;
        test_count++;
    end

    //========================================
    // TEST 5: Logical Operations
    //========================================
    $display("\n--- TEST 5: Logical Operations ---");
    is_8_bit = 0;
    flags_in = 16'h0000;

    a = 16'hFF00;
    b = 16'h0F0F;
    op = 6'd4;  // ALUOp_AND
    #1;
    if (out[15:0] == 16'h0F00) begin
        $display("[PASS] AND 0xFF00 & 0x0F0F = 0x0F00");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] AND: out=0x%04h", out[15:0]);
        fail_count++;
        test_count++;
    end

    a = 16'hF0F0;
    b = 16'h0F0F;
    op = 6'd6;  // ALUOp_OR
    #1;
    if (out[15:0] == 16'hFFFF) begin
        $display("[PASS] OR 0xF0F0 | 0x0F0F = 0xFFFF");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] OR: out=0x%04h", out[15:0]);
        fail_count++;
        test_count++;
    end

    a = 16'hAAAA;
    b = 16'h5555;
    op = 6'd5;  // ALUOp_XOR
    #1;
    if (out[15:0] == 16'hFFFF) begin
        $display("[PASS] XOR 0xAAAA ^ 0x5555 = 0xFFFF");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] XOR: out=0x%04h", out[15:0]);
        fail_count++;
        test_count++;
    end

    a = 16'h00FF;
    b = 16'h0000;
    op = 6'd22;  // ALUOp_NOT
    #1;
    if (out[15:0] == 16'hFF00) begin
        $display("[PASS] NOT 0x00FF = 0xFF00");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] NOT: out=0x%04h", out[15:0]);
        fail_count++;
        test_count++;
    end

    //========================================
    // TEST 6: Shift Operations (single bit)
    //========================================
    $display("\n--- TEST 6: Shift Operations ---");
    is_8_bit = 0;
    multibit_shift = 0;
    shift_count = 5'd1;
    flags_in = 16'h0000;

    // Shift left
    a = 16'h0004;
    op = 6'd16;  // ALUOp_SHL
    #1;
    if (out[15:0] == 16'h0008 && flags_out[CF_IDX] == 0) begin
        $display("[PASS] SHL 0x0004 << 1 = 0x0008");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] SHL: out=0x%04h, CF=%b", out[15:0], flags_out[CF_IDX]);
        fail_count++;
        test_count++;
    end

    // Shift right
    a = 16'h0008;
    op = 6'd15;  // ALUOp_SHR
    #1;
    if (out[15:0] == 16'h0004 && flags_out[CF_IDX] == 0) begin
        $display("[PASS] SHR 0x0008 >> 1 = 0x0004");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] SHR: out=0x%04h, CF=%b", out[15:0], flags_out[CF_IDX]);
        fail_count++;
        test_count++;
    end

    // Arithmetic shift right (sign extend)
    a = 16'h8000;
    op = 6'd17;  // ALUOp_SAR
    #1;
    if (out[15:0] == 16'hC000 && flags_out[CF_IDX] == 0) begin
        $display("[PASS] SAR 0x8000 >> 1 = 0xC000 (sign extended)");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] SAR: out=0x%04h, CF=%b", out[15:0], flags_out[CF_IDX]);
        fail_count++;
        test_count++;
    end

    //========================================
    // TEST 7: Rotate Operations
    //========================================
    $display("\n--- TEST 7: Rotate Operations ---");
    is_8_bit = 0;
    multibit_shift = 0;
    shift_count = 5'd1;
    flags_in = 16'h0000;

    // Rotate left
    a = 16'h8001;
    op = 6'd19;  // ALUOp_ROL
    #1;
    if (out[15:0] == 16'h0003 && flags_out[CF_IDX] == 1) begin
        $display("[PASS] ROL 0x8001 = 0x0003 with CF=1");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] ROL: out=0x%04h, CF=%b", out[15:0], flags_out[CF_IDX]);
        fail_count++;
        test_count++;
    end

    // Rotate right
    a = 16'h0003;
    op = 6'd18;  // ALUOp_ROR
    #1;
    if (out[15:0] == 16'h8001 && flags_out[CF_IDX] == 1) begin
        $display("[PASS] ROR 0x0003 = 0x8001 with CF=1");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] ROR: out=0x%04h, CF=%b", out[15:0], flags_out[CF_IDX]);
        fail_count++;
        test_count++;
    end

    //========================================
    // TEST 8: Flag Operations
    //========================================
    $display("\n--- TEST 8: Flag Operations ---");

    // Get flags
    flags_in = 16'hABCD;
    op = 6'd11;  // ALUOp_GETFLAGS
    check_result("GETFLAGS", 32'h0000ABCD);

    // Set flags from A
    a = 16'h1234;
    op = 6'd13;  // ALUOp_SETFLAGSA
    #1;
    if (flags_out == 16'h1234) begin
        $display("[PASS] SETFLAGSA: flags=0x%04h", flags_out);
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] SETFLAGSA: Expected 0x1234, got 0x%04h", flags_out);
        fail_count++;
        test_count++;
    end

    // Complement carry flag
    flags_in = 16'h0000;
    op = 6'd14;  // ALUOp_CMC
    #1;
    if (flags_out[CF_IDX] == 1) begin
        $display("[PASS] CMC: CF toggled to 1");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] CMC: CF=%b", flags_out[CF_IDX]);
        fail_count++;
        test_count++;
    end

    //========================================
    // Test Summary
    //========================================
    #10;
    $display("\n========================================");
    $display("ALU Testbench Complete");
    $display("========================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    if (fail_count == 0)
        $display("STATUS: ALL TESTS PASSED!");
    else
        $display("STATUS: SOME TESTS FAILED!");
    $display("========================================");

    $finish;
end

endmodule
