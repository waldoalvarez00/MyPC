// Copyright 2025, Waldo Alvarez
// Testbench for CPU-FPU Interface Integration
// Tests ESC instruction detection and FPU signaling

`timescale 1ns/1ps

module tb_fpu_interface();

    // Clock and reset
    logic clk;
    logic reset;

    // Core outputs to observe
    logic [7:0] fpu_opcode;
    logic [7:0] fpu_modrm;
    logic fpu_instr_valid;

    // FPU inputs to simulate
    logic fpu_busy;
    logic fpu_int;

    // Memory interface signals (minimal for test)
    logic [19:1] instr_m_addr;
    logic [15:0] instr_m_data_in;
    logic instr_m_access;
    logic instr_m_ack;

    logic [19:1] data_m_addr;
    logic [15:0] data_m_data_in;
    logic [15:0] data_m_data_out;
    logic data_m_access;
    logic data_m_ack;
    logic data_m_wr_en;
    logic [1:0] data_m_bytesel;
    logic d_io;

    // Interrupt signals
    logic nmi;
    logic intr;
    logic [7:0] irq;
    logic inta;

    // Debug signals
    logic debug_stopped;
    logic debug_seize;
    logic [15:0] debug_addr;
    logic debug_run;
    logic [15:0] debug_val;
    logic [15:0] debug_wr_val;
    logic debug_wr_en;

    logic lock;

    // Test control
    integer cycle_count;
    integer test_passed;
    integer test_failed;

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100 MHz clock
    end

    // Cycle counter
    always @(posedge clk) begin
        if (reset)
            cycle_count <= 0;
        else
            cycle_count <= cycle_count + 1;
    end

    // DUT - CPU Core
    Core core_inst (
        .clk(clk),
        .reset(reset),

        // Instruction bus
        .instr_m_addr(instr_m_addr),
        .instr_m_data_in(instr_m_data_in),
        .instr_m_access(instr_m_access),
        .instr_m_ack(instr_m_ack),

        // Data bus
        .data_m_addr(data_m_addr),
        .data_m_data_in(data_m_data_in),
        .data_m_data_out(data_m_data_out),
        .data_m_access(data_m_access),
        .data_m_ack(data_m_ack),
        .data_m_wr_en(data_m_wr_en),
        .data_m_bytesel(data_m_bytesel),
        .d_io(d_io),
        .lock(lock),

        // Interrupts
        .nmi(nmi),
        .intr(intr),
        .irq(irq),
        .inta(inta),

        // Debug
        .debug_stopped(debug_stopped),
        .debug_seize(debug_seize),
        .debug_addr(debug_addr),
        .debug_run(debug_run),
        .debug_val(debug_val),
        .debug_wr_val(debug_wr_val),
        .debug_wr_en(debug_wr_en),

        // FPU Interface
        .fpu_opcode(fpu_opcode),
        .fpu_modrm(fpu_modrm),
        .fpu_instr_valid(fpu_instr_valid),
        .fpu_busy(fpu_busy),
        .fpu_int(fpu_int)
    );

    // Monitor FPU signals
    always @(posedge clk) begin
        if (!reset && fpu_instr_valid) begin
            $display("[%04d] FPU INSTRUCTION VALID: opcode=0x%02h modrm=0x%02h",
                     cycle_count, fpu_opcode, fpu_modrm);
        end

        if (!reset && fpu_busy) begin
            $display("[%04d] FPU BUSY asserted - CPU should stall", cycle_count);
        end
    end

    // Simple instruction memory model
    // Provides ESC instructions for testing
    logic [15:0] instruction_memory [0:1023];

    initial begin
        // Initialize instruction memory with test program
        // NOP followed by ESC instructions

        instruction_memory[0] = 16'h9090;  // NOP NOP
        instruction_memory[1] = 16'hC0D8;  // ESC D8 C0 (FADD ST(0), ST(0))
        instruction_memory[2] = 16'h9090;  // NOP NOP
        instruction_memory[3] = 16'hE8D9;  // ESC D9 E8 (FLD1)
        instruction_memory[4] = 16'h9090;  // NOP NOP
        instruction_memory[5] = 16'hEED9;  // ESC D9 EE (FLDZ)
        instruction_memory[6] = 16'h9090;  // NOP NOP
        instruction_memory[7] = 16'hF0DB;  // ESC DB F0 (FENI)
    end

    // Instruction fetch response
    always @(posedge clk) begin
        instr_m_ack <= 1'b0;

        if (instr_m_access && !reset) begin
            instr_m_data_in <= instruction_memory[instr_m_addr[9:0]];
            instr_m_ack <= 1'b1;
        end
    end

    // Data memory response (simple ACK)
    always @(posedge clk) begin
        data_m_ack <= 1'b0;
        data_m_data_in <= 16'h0000;

        if (data_m_access && !reset) begin
            data_m_ack <= 1'b1;
        end
    end

    // Test stimulus
    initial begin
        $display("========================================");
        $display("CPU-FPU Interface Integration Test");
        $display("========================================");

        // Initialize
        reset = 1;
        fpu_busy = 0;
        fpu_int = 0;
        nmi = 0;
        intr = 0;
        irq = 8'h00;
        debug_seize = 0;
        debug_run = 0;
        debug_wr_en = 0;
        test_passed = 0;
        test_failed = 0;

        // Reset pulse
        repeat(5) @(posedge clk);
        reset = 0;
        $display("Reset released at cycle %0d", cycle_count);

        // TEST 1: Verify ESC D8 instruction detection
        $display("\nTEST 1: ESC D8 instruction detection");
        wait(fpu_opcode == 8'hD8 && fpu_instr_valid);
        @(posedge clk);
        if (fpu_opcode == 8'hD8 && fpu_modrm == 8'hC0) begin
            $display("  PASS: ESC D8 C0 detected correctly");
            test_passed = test_passed + 1;
        end else begin
            $display("  FAIL: Expected opcode=D8 modrm=C0, got opcode=%02h modrm=%02h",
                     fpu_opcode, fpu_modrm);
            test_failed = test_failed + 1;
        end

        // TEST 2: Verify ESC D9 instruction detection
        $display("\nTEST 2: ESC D9 instruction detection");
        wait(fpu_opcode == 8'hD9 && fpu_instr_valid);
        @(posedge clk);
        if (fpu_opcode == 8'hD9 && fpu_modrm == 8'hE8) begin
            $display("  PASS: ESC D9 E8 detected correctly");
            test_passed = test_passed + 1;
        end else begin
            $display("  FAIL: Expected opcode=D9 modrm=E8, got opcode=%02h modrm=%02h",
                     fpu_opcode, fpu_modrm);
            test_failed = test_failed + 1;
        end

        // TEST 3: Verify FPU busy stall
        $display("\nTEST 3: FPU busy stall");
        wait(fpu_opcode == 8'hD9 && fpu_instr_valid);
        @(posedge clk);

        // Assert FPU busy
        fpu_busy = 1;
        $display("  Asserting FPU busy signal");

        // Wait some cycles
        repeat(10) @(posedge clk);

        // Check that no new FPU instruction was issued while busy
        if (fpu_instr_valid == 0) begin
            $display("  PASS: CPU correctly stalled on FPU busy");
            test_passed = test_passed + 1;
        end else begin
            $display("  FAIL: CPU issued new instruction while FPU busy");
            test_failed = test_failed + 1;
        end

        // Clear FPU busy
        fpu_busy = 0;
        $display("  Clearing FPU busy signal");

        // Allow execution to continue
        repeat(20) @(posedge clk);

        // TEST 4: Verify ESC DB instruction detection
        $display("\nTEST 4: ESC DB instruction detection");
        wait(fpu_opcode == 8'hDB && fpu_instr_valid);
        @(posedge clk);
        if (fpu_opcode == 8'hDB && fpu_modrm == 8'hF0) begin
            $display("  PASS: ESC DB F0 detected correctly");
            test_passed = test_passed + 1;
        end else begin
            $display("  FAIL: Expected opcode=DB modrm=F0, got opcode=%02h modrm=%02h",
                     fpu_opcode, fpu_modrm);
            test_failed = test_failed + 1;
        end

        // Summary
        repeat(10) @(posedge clk);
        $display("\n========================================");
        $display("TEST SUMMARY");
        $display("========================================");
        $display("Tests Passed: %0d", test_passed);
        $display("Tests Failed: %0d", test_failed);

        if (test_failed == 0) begin
            $display("\n*** ALL TESTS PASSED ***");
            $finish(0);
        end else begin
            $display("\n*** SOME TESTS FAILED ***");
            $finish(1);
        end
    end

    // Timeout
    initial begin
        #100000;  // 100us timeout
        $display("\nERROR: Test timeout!");
        $finish(1);
    end

endmodule
