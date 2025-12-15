//============================================================================
//
//  FPU Error Detection in WAIT Instruction Testbench
//  Tests authentic 8087/8086 ERROR pin polling via FWAIT
//
//  Test Scenarios:
//  1. Normal FPU operation - WAIT completes when FPU not busy
//  2. Busy polling - WAIT loops while FPU is busy
//  3. FPU error detection - WAIT detects ERROR pin and triggers exception
//  4. Error persistence - ERROR signal persists across multiple WAITs
//
//  Copyright Waldo Alvarez, 2025
//  https://pipflow.com
//
//============================================================================

`timescale 1ns/1ps

`include "../Quartus/rtl/CPU/RegisterEnum.sv"
`include "../Quartus/rtl/CPU/MicrocodeTypes.sv"
`include "../Quartus/rtl/CPU/Instruction.sv"

module fpu_error_wait_tb;

//============================================================================
// Clock and Reset
//============================================================================

reg clk;
reg reset;

always #5 clk = ~clk;  // 100 MHz clock

//============================================================================
// DUT Signals - Microcode Module
//============================================================================

// Interrupt signals
reg nmi_pulse;
reg intr;
reg int_enabled;
wire inta;
wire irq_to_mdr;
wire start_interrupt;
wire do_escape_fault;

// Control signals
reg stall;
reg divide_error;
reg rm_is_reg;
reg [2:0] modrm_reg;
reg zf;
reg tf;
reg jump_taken;
reg rb_zero;
reg fpu_busy;      // BUSY pin from 8087
reg fpu_int;       // ERROR pin from 8087

// Microcode outputs
wire [15:0] microcode_immediate;
wire [8:0] update_flags;
wire modrm_start;
wire use_microcode_immediate;
wire [7:0] opcode;
wire lock;
wire multibit_shift;
wire is_hlt;
wire next_microinstruction;
wire starting_instruction;

// Microinstruction fields
wire [2:0] a_sel;
wire [5:0] alu_op;
wire [2:0] b_sel;
wire ext_int_yield;
wire io;
wire load_ip;
wire mar_wr_sel;
wire mar_write;
wire mdr_write;
wire mem_read;
wire mem_write;
wire next_instruction;
wire ra_modrm_rm_reg;
wire [2:0] ra_sel;
wire rb_cl;
wire [2:0] rd_sel;
wire [1:0] rd_sel_source;
wire [1:0] reg_wr_source;
wire [1:0] segment;
wire segment_force;
wire segment_wr_en;
wire tmp_wr_en;
wire tmp_wr_sel;
wire fpu_ctrl_wr;
wire width;
wire reg_wr_en;

// FIFO interface (simulated)
wire fifo_rd_en;
Instruction next_instruction_value;
Instruction cur_instruction;  // Output from DUT
reg fifo_empty;
reg fifo_resetting;

// Loop control
wire loop_next;
reg loop_done;

// Debug interface
wire debug_stopped;
reg debug_seize;
reg [7:0] debug_addr;
reg debug_run;

// Test tracking
integer test_count;
integer pass_count;
integer fail_count;
string test_name;
integer cycle_count;

// Pulse capture for INT trigger
reg int_detected;
reg [15:0] int_vector;
reg int_detected2;
reg [15:0] int_vector2;

//============================================================================
// DUT Instantiation
//============================================================================

Microcode dut (
    .clk(clk),
    .reset(reset),
    .nmi_pulse(nmi_pulse),
    .intr(intr),
    .inta(inta),
    .irq_to_mdr(irq_to_mdr),
    .start_interrupt(start_interrupt),
    .do_escape_fault(do_escape_fault),
    .starting_instruction(starting_instruction),
    .stall(stall),
    .divide_error(divide_error),
    .rm_is_reg(rm_is_reg),
    .modrm_reg(modrm_reg),
    .int_enabled(int_enabled),
    .zf(zf),
    .tf(tf),
    .microcode_immediate(microcode_immediate),
    .update_flags(update_flags),
    .modrm_start(modrm_start),
    .use_microcode_immediate(use_microcode_immediate),
    .opcode(opcode),
    .jump_taken(jump_taken),
    .rb_zero(rb_zero),
    .fpu_busy(fpu_busy),
    .fpu_int(fpu_int),       // NEW: FPU ERROR pin
    .lock(lock),
    .multibit_shift(multibit_shift),
    .is_hlt(is_hlt),
    .next_microinstruction(next_microinstruction),
    .a_sel(a_sel),
    .alu_op(alu_op),
    .b_sel(b_sel),
    .ext_int_yield(ext_int_yield),
    .io(io),
    .load_ip(load_ip),
    .mar_wr_sel(mar_wr_sel),
    .mar_write(mar_write),
    .mdr_write(mdr_write),
    .mem_read(mem_read),
    .mem_write(mem_write),
    .next_instruction(next_instruction),
    .ra_modrm_rm_reg(ra_modrm_rm_reg),
    .ra_sel(ra_sel),
    .rb_cl(rb_cl),
    .rd_sel(rd_sel),
    .rd_sel_source(rd_sel_source),
    .reg_wr_en(reg_wr_en),
    .reg_wr_source(reg_wr_source),
    .segment(segment),
    .segment_force(segment_force),
    .segment_wr_en(segment_wr_en),
    .tmp_wr_en(tmp_wr_en),
    .tmp_wr_sel(tmp_wr_sel),
    .fpu_ctrl_wr(fpu_ctrl_wr),
    .width(width),
    .fifo_rd_en(fifo_rd_en),
    .cur_instruction(cur_instruction),
    .next_instruction_value(next_instruction_value),
    .fifo_empty(fifo_empty),
    .fifo_resetting(fifo_resetting),
    .loop_next(loop_next),
    .loop_done(loop_done),
    .debug_stopped(debug_stopped),
    .debug_seize(debug_seize),
    .debug_addr(debug_addr),
    .debug_run(debug_run)
);

//============================================================================
// Load Microcode ROM - CRITICAL!
//============================================================================

initial begin
    $readmemb("microcode.bin", dut.mem);
end

//============================================================================
// Test Procedures
//============================================================================

task create_instruction;
    input [7:0] opcode_val;
    input has_modrm_val;
    input invalid_val;
    input RepPrefix rep_val;
    input lock_val;
begin
    next_instruction_value.opcode = opcode_val;
    next_instruction_value.has_modrm = has_modrm_val;
    next_instruction_value.invalid = invalid_val;
    next_instruction_value.rep = rep_val;
    next_instruction_value.lock = lock_val;
    next_instruction_value.has_segment_override = 1'b0;
    next_instruction_value.segment = ES;
    next_instruction_value.mod_rm = 8'hc0;  // reg-reg mode
    next_instruction_value.displacement = 16'h0000;
    next_instruction_value.immediates[0] = 16'h1234;
    next_instruction_value.immediates[1] = 16'h5678;
    next_instruction_value.length = 4'd1;
end
endtask

task reset_system;
    integer boot_cycles;
    integer i;
begin
    reset = 1;
    nmi_pulse = 0;
    intr = 0;
    int_enabled = 0;
    stall = 0;
    divide_error = 0;
    rm_is_reg = 1;  // Register mode
    modrm_reg = 0;
    zf = 0;
    tf = 0;
    jump_taken = 0;
    rb_zero = 0;
    fpu_busy = 0;
    fpu_int = 0;
    fifo_empty = 1;  // FIFO starts empty!
    fifo_resetting = 0;
    loop_done = 0;
    debug_seize = 0;
    debug_addr = 0;
    debug_run = 0;

    // Create FWAIT instruction (0x9B)
    create_instruction(8'h9B, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);

    // Release reset
    #100;
    reset = 0;

    // Wait for boot sequence to complete
    boot_cycles = 0;
    for (i = 0; i < 100; i = i + 1) begin
        @(posedge clk);
        boot_cycles = boot_cycles + 1;

        // Break if we see next_instruction (boot complete)
        if (next_instruction || starting_instruction) begin
            i = 100; // Exit loop
        end
    end

    #40;  // Additional settling time
end
endtask

task wait_cycles;
    input integer n;
    integer i;
begin
    for (i = 0; i < n; i = i + 1) begin
        @(posedge clk);
    end
end
endtask

task wait_for_instruction_start;
    integer timeout;
begin
    timeout = 0;
    while (!starting_instruction && timeout < 50) begin
        @(posedge clk);
        timeout = timeout + 1;
    end
    if (timeout >= 50) begin
        $display("[WARN] Timeout waiting for instruction start");
    end
end
endtask

task wait_for_next_instruction;
    integer timeout;
begin
    timeout = 0;
    while (!next_instruction && timeout < 100) begin
        @(posedge clk);
        timeout = timeout + 1;
    end
    if (timeout >= 100) begin
        $display("[WARN] Timeout waiting for next_instruction");
    end
end
endtask

task check_result;
    input string name;
    input logic expected;
    input logic actual;
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] %s: Expected %b, Got %b", name, expected, actual);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] %s: Expected %b, Got %b", name, expected, actual);
        fail_count = fail_count + 1;
    end
end
endtask

task monitor_signals;
    input integer max_cycles;
    integer i;
begin
    $display("  Monitoring for %0d cycles:", max_cycles);
    for (i = 0; i < max_cycles; i = i + 1) begin
        $display("    Cycle %3d: busy=%b int=%b next=%b start=%b tmp_wr=%b imm=0x%04h",
                 i, fpu_busy, fpu_int, next_instruction, starting_instruction,
                 tmp_wr_en, microcode_immediate);
        @(posedge clk);
    end
end
endtask

// New task: Monitor for INT trigger and capture pulse
task monitor_for_int_trigger;
    input integer max_cycles;
    output reg detected;
    output reg [15:0] vector;
    integer i;
begin
    detected = 0;
    vector = 16'h0;
    for (i = 0; i < max_cycles; i = i + 1) begin
        if (tmp_wr_en && microcode_immediate == 16'h10) begin
            detected = 1;
            vector = microcode_immediate;
            $display("    [CAPTURED] Cycle %0d: INT trigger detected, vector=0x%04h", i, vector);
        end
        @(posedge clk);
    end
end
endtask

//============================================================================
// Test Cases
//============================================================================

initial begin
    clk = 0;
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    cycle_count = 0;

    $display("======================================================================");
    $display("FPU Error Detection in WAIT Instruction Test");
    $display("Testing authentic 8087/8086 ERROR pin polling");
    $display("======================================================================");

    //------------------------------------------------------------------------
    // Test 1: Normal WAIT completion (FPU not busy, no error)
    //------------------------------------------------------------------------
    test_name = "Normal WAIT - Not busy, no error";
    $display("\nTest 1: %s", test_name);
    reset_system();

    // Set up test conditions
    fpu_busy = 0;
    fpu_int = 0;

    // Present FWAIT instruction to sequencer
    $display("  Setting up FWAIT instruction (0x9B)...");
    fifo_empty = 0;  // Make instruction available
    create_instruction(8'h9B, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);

    wait_for_instruction_start();
    $display("  WAIT instruction started");

    // Wait for FIFO read and cur_instruction update
    @(posedge clk);  // FIFO read cycle
    @(posedge clk);  // cur_instruction updated

    // Monitor execution for a few cycles
    $display("  Monitoring WAIT execution:");
    monitor_signals(10);

    // WAIT should complete quickly when FPU not busy and no error
    check_result("Next instruction signaled", 1'b1, next_instruction);

    //------------------------------------------------------------------------
    // Test 2: WAIT polling while FPU busy
    //------------------------------------------------------------------------
    test_name = "WAIT polling while FPU busy";
    $display("\nTest 2: %s", test_name);
    reset_system();

    // Set up test conditions - FPU is busy
    fpu_busy = 1;  // FPU still executing
    fpu_int = 0;

    // Present FWAIT instruction
    $display("  Setting up FWAIT instruction while FPU busy...");
    fifo_empty = 0;
    create_instruction(8'h9B, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);

    wait_for_instruction_start();
    $display("  WAIT instruction started, FPU busy");

    // Wait for FIFO read and cur_instruction update
    @(posedge clk);
    @(posedge clk);

    // Should stay in polling loop while busy
    $display("  Checking polling behavior...");
    wait_cycles(5);
    check_result("Should not complete while busy", 1'b0, next_instruction);

    // Clear busy
    $display("  Clearing FPU busy");
    fpu_busy = 0;
    wait_for_next_instruction();

    check_result("Should complete after busy clears", 1'b1, next_instruction);

    //------------------------------------------------------------------------
    // Test 3: FPU error detection (ERROR pin asserted)
    //------------------------------------------------------------------------
    test_name = "FPU error detection";
    $display("\nTest 3: %s", test_name);
    reset_system();

    // Set up test conditions - FPU error present
    fpu_busy = 0;
    fpu_int = 1;   // FPU ERROR pin asserted

    // Present FWAIT instruction
    $display("  Setting up FWAIT instruction with FPU error...");
    fifo_empty = 0;
    create_instruction(8'h9B, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);

    wait_for_instruction_start();
    $display("  WAIT instruction started, FPU error asserted");

    // Wait for FIFO read and cur_instruction update
    @(posedge clk);
    @(posedge clk);

    // Monitor for error handling (capture INT trigger pulse)
    $display("  Monitoring error detection...");
    monitor_for_int_trigger(15, int_detected, int_vector);

    // Should detect error and prepare for INT 16 (0x10)
    // Microcode should write 0x10 to TMP and jump to interrupt handler
    check_result("TMP write for INT vector", 1'b1, int_detected);
    check_result("Immediate value is 0x10", 1'b1, int_vector == 16'h10);

    //------------------------------------------------------------------------
    // Test 4: FPU busy then error sequence
    //------------------------------------------------------------------------
    test_name = "FPU busy then error sequence";
    $display("\nTest 4: %s", test_name);
    reset_system();

    // Set up test conditions - FPU busy, then will signal error
    fpu_busy = 1;
    fpu_int = 0;

    // Present FWAIT instruction
    $display("  Setting up FWAIT instruction while FPU busy...");
    fifo_empty = 0;
    create_instruction(8'h9B, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);

    wait_for_instruction_start();
    $display("  WAIT instruction started, FPU busy");

    // Wait for FIFO read and cur_instruction update
    @(posedge clk);
    @(posedge clk);

    // Poll for a few cycles while busy
    $display("  Polling while FPU busy...");
    wait_cycles(5);

    // While busy, should still be polling (not checking error yet)
    check_result("Not checking error while busy", 1'b0, tmp_wr_en);

    // FPU completes with error
    $display("  FPU completes with error");
    fpu_busy = 0;
    fpu_int = 1;

    // Monitor error detection (capture INT trigger pulse)
    $display("  Monitoring error detection after busy clears...");
    monitor_for_int_trigger(15, int_detected2, int_vector2);

    // Should detect error after busy clears
    check_result("Error detected after busy clears", 1'b1, int_detected2);

    //------------------------------------------------------------------------
    // Test Summary
    //------------------------------------------------------------------------
    $display("\n======================================================================");
    $display("Test Summary");
    $display("======================================================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);

    if (fail_count == 0) begin
        $display("\n*** ALL TESTS PASSED! ***");
        $display("FPU ERROR pin detection working correctly via FWAIT microcode");
        $display("Authentic 8087/8086 polling architecture validated");
    end else begin
        $display("\n*** SOME TESTS FAILED ***");
        $display("Note: This tests the microcode-level ERROR pin polling");
        $display("Verify wait.us microcode and JumpType_FPU_ERROR implementation");
    end
    $display("======================================================================\n");

    $finish;
end

//============================================================================
// Timeout watchdog
//============================================================================

initial begin
    #500000;  // 500 us timeout
    $display("\n[ERROR] Testbench timeout!");
    $display("Test hung - likely infinite loop in microcode");
    $finish;
end

endmodule
