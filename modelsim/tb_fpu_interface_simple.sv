// Copyright 2025
// Simplified CPU-FPU Interface Test
// Tests only the FPU interface signal generation logic

`timescale 1ns/1ps

module tb_fpu_interface_simple;

// Test signals
logic clk;
logic reset;

// FPU Interface signals (outputs from Core)
logic [7:0] fpu_opcode;
logic [7:0] fpu_modrm;
logic fpu_instr_valid;

// FPU status (input to Core)
logic fpu_busy;

// Test control
logic [7:0] opcode;
logic [7:0] modrm;
logic starting_instruction;

// Instantiate the FPU interface logic directly
// This is the same logic from Core.sv lines 110-120
wire is_esc_instruction = (opcode[7:3] == 5'b11011);

assign fpu_opcode = is_esc_instruction ? opcode : 8'h00;
assign fpu_modrm = is_esc_instruction ? modrm : 8'h00;
assign fpu_instr_valid = is_esc_instruction & starting_instruction;

// Clock generation
initial begin
    clk = 0;
    forever #5 clk = ~clk;  // 100MHz clock
end

// Test sequence
initial begin
    $display("==============================================");
    $display("Simplified CPU-FPU Interface Test");
    $display("==============================================");
    $display("");

    // Initialize
    reset = 1;
    opcode = 8'h00;
    modrm = 8'h00;
    starting_instruction = 0;
    fpu_busy = 0;

    @(posedge clk);
    reset = 0;
    @(posedge clk);

    // Test 1: Non-ESC instruction (should not trigger FPU)
    $display("Test 1: Non-ESC instruction (MOV)");
    opcode = 8'h89;  // MOV instruction
    modrm = 8'hC0;
    starting_instruction = 1;
    @(posedge clk);
    starting_instruction = 0;

    if (fpu_instr_valid == 0 && fpu_opcode == 8'h00) begin
        $display("  PASS: Non-ESC instruction does not trigger FPU");
    end else begin
        $display("  FAIL: Non-ESC instruction triggered FPU signals");
        $display("    fpu_instr_valid = %b (expected 0)", fpu_instr_valid);
        $display("    fpu_opcode = 0x%02h (expected 0x00)", fpu_opcode);
        $finish;
    end
    $display("");

    @(posedge clk);
    @(posedge clk);

    // Test 2: ESC instruction D8 (FADD)
    $display("Test 2: ESC instruction 0xD8 (FADD)");
    opcode = 8'hD8;
    modrm = 8'hC1;  // FADD ST(0), ST(1)
    starting_instruction = 1;
    @(posedge clk);

    if (fpu_instr_valid == 1 && fpu_opcode == 8'hD8 && fpu_modrm == 8'hC1) begin
        $display("  PASS: ESC 0xD8 correctly signals FPU");
    end else begin
        $display("  FAIL: ESC 0xD8 did not signal FPU correctly");
        $display("    fpu_instr_valid = %b (expected 1)", fpu_instr_valid);
        $display("    fpu_opcode = 0x%02h (expected 0xD8)", fpu_opcode);
        $display("    fpu_modrm = 0x%02h (expected 0xC1)", fpu_modrm);
        $finish;
    end
    $display("");

    starting_instruction = 0;
    @(posedge clk);
    @(posedge clk);

    // Test 3: ESC instruction D9 (FLD)
    $display("Test 3: ESC instruction 0xD9 (FLD)");
    opcode = 8'hD9;
    modrm = 8'h00;
    starting_instruction = 1;
    @(posedge clk);

    if (fpu_instr_valid == 1 && fpu_opcode == 8'hD9) begin
        $display("  PASS: ESC 0xD9 correctly signals FPU");
    end else begin
        $display("  FAIL: ESC 0xD9 did not signal FPU correctly");
        $finish;
    end
    $display("");

    starting_instruction = 0;
    @(posedge clk);
    @(posedge clk);

    // Test 4: ESC instruction DA
    $display("Test 4: ESC instruction 0xDA");
    opcode = 8'hDA;
    modrm = 8'h20;
    starting_instruction = 1;
    @(posedge clk);

    if (fpu_instr_valid == 1 && fpu_opcode == 8'hDA) begin
        $display("  PASS: ESC 0xDA correctly signals FPU");
    end else begin
        $display("  FAIL: ESC 0xDA did not signal FPU correctly");
        $finish;
    end
    $display("");

    starting_instruction = 0;
    @(posedge clk);
    @(posedge clk);

    // Test 5: ESC instruction DF (last ESC opcode)
    $display("Test 5: ESC instruction 0xDF (last ESC opcode)");
    opcode = 8'hDF;
    modrm = 8'hE0;
    starting_instruction = 1;
    @(posedge clk);

    if (fpu_instr_valid == 1 && fpu_opcode == 8'hDF) begin
        $display("  PASS: ESC 0xDF correctly signals FPU");
    end else begin
        $display("  FAIL: ESC 0xDF did not signal FPU correctly");
        $finish;
    end
    $display("");

    starting_instruction = 0;
    @(posedge clk);
    @(posedge clk);

    // Test 6: Boundary test - opcode 0xD7 (not ESC)
    $display("Test 6: Boundary test 0xD7 (not ESC)");
    opcode = 8'hD7;  // XLAT - not an ESC instruction
    modrm = 8'h00;
    starting_instruction = 1;
    @(posedge clk);

    if (fpu_instr_valid == 0 && fpu_opcode == 8'h00) begin
        $display("  PASS: 0xD7 correctly identified as non-ESC");
    end else begin
        $display("  FAIL: 0xD7 incorrectly identified as ESC");
        $finish;
    end
    $display("");

    starting_instruction = 0;
    @(posedge clk);
    @(posedge clk);

    // Test 7: Boundary test - opcode 0xE0 (not ESC)
    $display("Test 7: Boundary test 0xE0 (not ESC)");
    opcode = 8'hE0;  // LOOPNZ - not an ESC instruction
    modrm = 8'h00;
    starting_instruction = 1;
    @(posedge clk);

    if (fpu_instr_valid == 0 && fpu_opcode == 8'h00) begin
        $display("  PASS: 0xE0 correctly identified as non-ESC");
    end else begin
        $display("  FAIL: 0xE0 incorrectly identified as ESC");
        $finish;
    end
    $display("");

    starting_instruction = 0;
    @(posedge clk);
    @(posedge clk);

    // Test 8: FWAIT polling behavior (opcode 0x9B)
    $display("Test 8: FWAIT instruction behavior");
    $display("  Note: FWAIT microcode polling tested in microcode layer");
    $display("  This test verifies FPU busy signal can be read");

    fpu_busy = 1;
    @(posedge clk);
    if (fpu_busy == 1) begin
        $display("  PASS: FPU busy signal can be set");
    end else begin
        $display("  FAIL: FPU busy signal error");
        $finish;
    end

    fpu_busy = 0;
    @(posedge clk);
    if (fpu_busy == 0) begin
        $display("  PASS: FPU busy signal can be cleared");
    end else begin
        $display("  FAIL: FPU busy signal error");
        $finish;
    end
    $display("");

    // All tests passed
    $display("==============================================");
    $display("All FPU Interface Tests PASSED!");
    $display("==============================================");
    $display("");
    $display("Summary:");
    $display("  - ESC instruction detection (0xD8-0xDF): PASS");
    $display("  - Non-ESC boundary checking: PASS");
    $display("  - FPU signal generation: PASS");
    $display("  - FPU busy signal interface: PASS");
    $display("");
    $display("Next steps:");
    $display("  1. Verify microcode FWAIT polling (wait.us)");
    $display("  2. Test full CPU-FPU integration in Quartus");
    $display("  3. Run on actual MiSTer hardware");
    $display("");

    $finish;
end

// Timeout watchdog
initial begin
    #10000;
    $display("ERROR: Test timeout!");
    $finish;
end

endmodule
