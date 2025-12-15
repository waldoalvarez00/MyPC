// Testbench for ModRMDecode module
// Tests x86 ModR/M byte decoding for addressing modes

`timescale 1ns/1ps

module modrm_decode_tb;

    // Clock and reset
    logic        clk;
    logic        reset;

    // Control signals
    logic        start;
    logic        clear;
    logic [7:0]  modrm;
    logic [15:0] displacement;

    // Register inputs (for effective address calculation)
    logic [15:0] si;
    logic [15:0] di;
    logic [15:0] bp;
    logic [15:0] bx;

    // Outputs
    logic [15:0] effective_address;
    logic [2:0]  regnum;
    logic        rm_is_reg;
    logic [2:0]  rm_regnum;
    logic        bp_as_base;

    // Test tracking
    int test_num = 0;
    int errors = 0;
    int passed_tests = 0;

    // DUT instantiation
    ModRMDecode dut(
        .clk(clk),
        .reset(reset),
        .start(start),
        .clear(clear),
        .modrm(modrm),
        .displacement(displacement),
        .si(si),
        .di(di),
        .bp(bp),
        .bx(bx),
        .effective_address(effective_address),
        .regnum(regnum),
        .rm_is_reg(rm_is_reg),
        .rm_regnum(rm_regnum),
        .bp_as_base(bp_as_base)
    );

    // Clock generation: 50 MHz
    initial begin
        clk = 0;
        forever #10 clk = ~clk;  // 20ns period = 50 MHz
    end

    // Test stimulus
    initial begin
        $display("========================================");
        $display("ModRMDecode Unit Test");
        $display("========================================");

        // Initialize signals
        reset = 1;
        start = 0;
        clear = 0;
        modrm = 8'h00;
        displacement = 16'h0000;
        si = 16'h1000;
        di = 16'h2000;
        bp = 16'h3000;
        bx = 16'h4000;

        // Apply reset
        repeat(5) @(posedge clk);
        reset = 0;
        repeat(2) @(posedge clk);

        // Test MOD=11 (register-to-register) cases
        test_1_mod11_reg_to_reg();

        // Test MOD=00 (no displacement) addressing modes
        test_2_mod00_bx_si();
        test_3_mod00_bx_di();
        test_4_mod00_bp_si();
        test_5_mod00_bp_di();
        test_6_mod00_si();
        test_7_mod00_di();
        test_8_mod00_direct();
        test_9_mod00_bx();

        // Test MOD=01 (8-bit displacement) addressing modes
        test_10_mod01_bx_si_disp8();
        test_11_mod01_bp_di_disp8();

        // Test MOD=10 (16-bit displacement) addressing modes
        test_12_mod10_bx_si_disp16();
        test_13_mod10_bp_di_disp16();

        // Test register field extraction
        test_14_reg_field();

        // Test bp_as_base flag
        test_15_bp_as_base_flag();

        // Final results
        repeat(10) @(posedge clk);
        $display("\n========================================");
        $display("Test Summary:");
        $display("  Total Tests: %0d", test_num);
        $display("  Passed:      %0d", passed_tests);
        $display("  Failed:      %0d", errors);
        $display("========================================");

        if (errors == 0)
            $display("✓ ALL TESTS PASSED");
        else
            $display("✗ SOME TESTS FAILED");

        $finish;
    end

    // Task: Decode ModRM byte
    task decode_modrm(
        input [7:0]  mod_rm,
        input [15:0] disp
    );
        begin
            // Set inputs
            modrm = mod_rm;
            displacement = disp;

            // Pulse start signal
            @(posedge clk);
            start = 1;
            @(posedge clk);
            start = 0;

            // Wait for outputs to settle (ModRMDecode uses always_ff)
            repeat(3) @(posedge clk);
        end
    endtask

    // Test 1: MOD=11 (register mode) - should set rm_is_reg
    task test_1_mod11_reg_to_reg();
        begin
            test_num++;
            $display("\nTest %0d: MOD=11 (register-to-register)", test_num);

            // ModRM = 11_010_011 (MOD=11, REG=010/DX, RM=011/BX)
            decode_modrm(8'b11_010_011, 16'h0000);

            if (rm_is_reg && regnum == 3'd2 && rm_regnum == 3'd3) begin
                $display("  ✓ Register mode detected: REG=%0d, RM=%0d", regnum, rm_regnum);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: rm_is_reg=%b, regnum=%0d, rm_regnum=%0d",
                         rm_is_reg, regnum, rm_regnum);
                errors++;
            end
        end
    endtask

    // Test 2: MOD=00, RM=000 ([BX+SI])
    task test_2_mod00_bx_si();
        begin
            test_num++;
            $display("\nTest %0d: MOD=00, RM=000 ([BX+SI])", test_num);

            // Setup registers
            bx = 16'h1000;
            si = 16'h0200;

            // ModRM = 00_000_000 (MOD=00, REG=000, RM=000)
            decode_modrm(8'b00_000_000, 16'h0000);

            if (!rm_is_reg && effective_address == 16'h1200) begin
                $display("  ✓ Effective address correct: 0x%04X", effective_address);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected EA=0x1200, got 0x%04X, rm_is_reg=%b",
                         effective_address, rm_is_reg);
                errors++;
            end
        end
    endtask

    // Test 3: MOD=00, RM=001 ([BX+DI])
    task test_3_mod00_bx_di();
        begin
            test_num++;
            $display("\nTest %0d: MOD=00, RM=001 ([BX+DI])", test_num);

            bx = 16'h2000;
            di = 16'h0300;

            decode_modrm(8'b00_000_001, 16'h0000);

            if (!rm_is_reg && effective_address == 16'h2300) begin
                $display("  ✓ Effective address correct: 0x%04X", effective_address);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected EA=0x2300, got 0x%04X",
                         effective_address);
                errors++;
            end
        end
    endtask

    // Test 4: MOD=00, RM=010 ([BP+SI])
    task test_4_mod00_bp_si();
        begin
            test_num++;
            $display("\nTest %0d: MOD=00, RM=010 ([BP+SI])", test_num);

            bp = 16'h3000;
            si = 16'h0400;

            decode_modrm(8'b00_000_010, 16'h0000);

            if (!rm_is_reg && effective_address == 16'h3400 && bp_as_base) begin
                $display("  ✓ Effective address correct: 0x%04X, bp_as_base=%b",
                         effective_address, bp_as_base);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected EA=0x3400, got 0x%04X, bp_as_base=%b",
                         effective_address, bp_as_base);
                errors++;
            end
        end
    endtask

    // Test 5: MOD=00, RM=011 ([BP+DI])
    task test_5_mod00_bp_di();
        begin
            test_num++;
            $display("\nTest %0d: MOD=00, RM=011 ([BP+DI])", test_num);

            bp = 16'h4000;
            di = 16'h0500;

            decode_modrm(8'b00_000_011, 16'h0000);

            if (!rm_is_reg && effective_address == 16'h4500 && bp_as_base) begin
                $display("  ✓ Effective address correct: 0x%04X, bp_as_base=%b",
                         effective_address, bp_as_base);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected EA=0x4500, got 0x%04X, bp_as_base=%b",
                         effective_address, bp_as_base);
                errors++;
            end
        end
    endtask

    // Test 6: MOD=00, RM=100 ([SI])
    task test_6_mod00_si();
        begin
            test_num++;
            $display("\nTest %0d: MOD=00, RM=100 ([SI])", test_num);

            si = 16'h5000;

            decode_modrm(8'b00_000_100, 16'h0000);

            if (!rm_is_reg && effective_address == 16'h5000) begin
                $display("  ✓ Effective address correct: 0x%04X", effective_address);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected EA=0x5000, got 0x%04X",
                         effective_address);
                errors++;
            end
        end
    endtask

    // Test 7: MOD=00, RM=101 ([DI])
    task test_7_mod00_di();
        begin
            test_num++;
            $display("\nTest %0d: MOD=00, RM=101 ([DI])", test_num);

            di = 16'h6000;

            decode_modrm(8'b00_000_101, 16'h0000);

            if (!rm_is_reg && effective_address == 16'h6000) begin
                $display("  ✓ Effective address correct: 0x%04X", effective_address);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected EA=0x6000, got 0x%04X",
                         effective_address);
                errors++;
            end
        end
    endtask

    // Test 8: MOD=00, RM=110 (direct addressing [disp16])
    task test_8_mod00_direct();
        begin
            test_num++;
            $display("\nTest %0d: MOD=00, RM=110 (direct [disp16])", test_num);

            decode_modrm(8'b00_000_110, 16'h1234);

            if (!rm_is_reg && effective_address == 16'h1234) begin
                $display("  ✓ Direct address correct: 0x%04X", effective_address);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected EA=0x1234, got 0x%04X",
                         effective_address);
                errors++;
            end
        end
    endtask

    // Test 9: MOD=00, RM=111 ([BX])
    task test_9_mod00_bx();
        begin
            test_num++;
            $display("\nTest %0d: MOD=00, RM=111 ([BX])", test_num);

            bx = 16'h7000;

            decode_modrm(8'b00_000_111, 16'h0000);

            if (!rm_is_reg && effective_address == 16'h7000) begin
                $display("  ✓ Effective address correct: 0x%04X", effective_address);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected EA=0x7000, got 0x%04X",
                         effective_address);
                errors++;
            end
        end
    endtask

    // Test 10: MOD=01, RM=000 ([BX+SI+disp8])
    task test_10_mod01_bx_si_disp8();
        begin
            test_num++;
            $display("\nTest %0d: MOD=01, RM=000 ([BX+SI+disp8])", test_num);

            bx = 16'h1000;
            si = 16'h0200;

            // ModRM = 01_000_000, displacement = 0x0010 (8-bit disp, sign-extended)
            decode_modrm(8'b01_000_000, 16'h0010);

            if (!rm_is_reg && effective_address == 16'h1210) begin
                $display("  ✓ Effective address correct: 0x%04X", effective_address);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected EA=0x1210, got 0x%04X",
                         effective_address);
                errors++;
            end
        end
    endtask

    // Test 11: MOD=01, RM=011 ([BP+DI+disp8])
    task test_11_mod01_bp_di_disp8();
        begin
            test_num++;
            $display("\nTest %0d: MOD=01, RM=011 ([BP+DI+disp8])", test_num);

            bp = 16'h2000;
            di = 16'h0300;

            decode_modrm(8'b01_000_011, 16'h0020);

            if (!rm_is_reg && effective_address == 16'h2320 && bp_as_base) begin
                $display("  ✓ Effective address correct: 0x%04X, bp_as_base=%b",
                         effective_address, bp_as_base);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected EA=0x2320, got 0x%04X, bp_as_base=%b",
                         effective_address, bp_as_base);
                errors++;
            end
        end
    endtask

    // Test 12: MOD=10, RM=000 ([BX+SI+disp16])
    task test_12_mod10_bx_si_disp16();
        begin
            test_num++;
            $display("\nTest %0d: MOD=10, RM=000 ([BX+SI+disp16])", test_num);

            bx = 16'h1000;
            si = 16'h0200;

            decode_modrm(8'b10_000_000, 16'h1000);

            if (!rm_is_reg && effective_address == 16'h2200) begin
                $display("  ✓ Effective address correct: 0x%04X", effective_address);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected EA=0x2200, got 0x%04X",
                         effective_address);
                errors++;
            end
        end
    endtask

    // Test 13: MOD=10, RM=011 ([BP+DI+disp16])
    task test_13_mod10_bp_di_disp16();
        begin
            test_num++;
            $display("\nTest %0d: MOD=10, RM=011 ([BP+DI+disp16])", test_num);

            bp = 16'h3000;
            di = 16'h0400;

            decode_modrm(8'b10_000_011, 16'h2000);

            if (!rm_is_reg && effective_address == 16'h5400 && bp_as_base) begin
                $display("  ✓ Effective address correct: 0x%04X, bp_as_base=%b",
                         effective_address, bp_as_base);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected EA=0x5400, got 0x%04X, bp_as_base=%b",
                         effective_address, bp_as_base);
                errors++;
            end
        end
    endtask

    // Test 14: Register field extraction (all REG values)
    task test_14_reg_field();
        begin
            test_num++;
            $display("\nTest %0d: Register field extraction", test_num);

            // Test REG=101 (BP register)
            decode_modrm(8'b11_101_000, 16'h0000);

            if (regnum == 3'd5) begin
                $display("  ✓ REG field correctly extracted: %0d", regnum);
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: Expected REG=5, got %0d", regnum);
                errors++;
            end
        end
    endtask

    // Test 15: bp_as_base flag for different modes
    task test_15_bp_as_base_flag();
        begin
            test_num++;
            $display("\nTest %0d: bp_as_base flag verification", test_num);

            // MOD=01, RM=110 should set bp_as_base
            decode_modrm(8'b01_000_110, 16'h0100);

            if (bp_as_base) begin
                $display("  ✓ bp_as_base correctly set for MOD=01, RM=110");
                passed_tests++;
            end else begin
                $display("  ✗ FAILED: bp_as_base should be set");
                errors++;
            end
        end
    endtask

    // Timeout watchdog
    initial begin
        #500000;  // 500us timeout
        $display("\n✗ TIMEOUT: Test did not complete");
        $finish;
    end

endmodule
