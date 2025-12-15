/**
 * fpu_wait_minimal_tb.sv
 *
 * Minimal testbench for FWAIT instruction with FPU ERROR pin detection
 *
 * Tests:
 * 1. FWAIT completes when FPU not busy and no error
 * 2. FWAIT polls while FPU busy
 * 3. FWAIT detects ERROR pin and triggers INT 16
 *
 * This follows the working microcode_tb pattern exactly.
 */

`timescale 1ns/1ps

`include "../Quartus/rtl/CPU/RegisterEnum.sv"
`include "../Quartus/rtl/CPU/MicrocodeTypes.sv"
`include "../Quartus/rtl/CPU/Instruction.sv"

module fpu_wait_minimal_tb;

//============================================================================
// Clock and Reset
//============================================================================

reg clk;
reg reset;

always #5 clk = ~clk;  // 100 MHz

//============================================================================
// Microcode Interface Signals
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
reg fpu_busy;
reg fpu_int;

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

// FIFO interface
wire fifo_rd_en;
Instruction next_instruction_value;
Instruction cur_instruction;
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
    .fpu_int(fpu_int),
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
    .reg_wr_source(reg_wr_source),
    .segment(segment),
    .segment_force(segment_force),
    .segment_wr_en(segment_wr_en),
    .tmp_wr_en(tmp_wr_en),
    .tmp_wr_sel(tmp_wr_sel),
    .fpu_ctrl_wr(fpu_ctrl_wr),
    .width(width),
    .reg_wr_en(reg_wr_en),
    .fifo_rd_en(fifo_rd_en),
    .next_instruction_value(next_instruction_value),
    .cur_instruction(cur_instruction),
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
// Load Microcode ROM
//============================================================================

initial begin
    $readmemb("microcode.bin", dut.mem);
end

//============================================================================
// Test Tasks
//============================================================================

task check_result;
    input logic expected;
    input logic actual;
    input string test_name;
begin
    test_count = test_count + 1;
    if (expected === actual) begin
        $display("[PASS] Test %0d: %s", test_count, test_name);
        pass_count = pass_count + 1;
    end else begin
        $display("[FAIL] Test %0d: %s - Expected %b, Got %b", test_count, test_name, expected, actual);
        fail_count = fail_count + 1;
    end
end
endtask

task create_instruction;
    input [7:0] opcode_val;
    input logic has_modrm_val;
    input logic invalid_val;
    input RepPrefix rep_val;
    input logic lock_val;
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

task wait_for_instruction_start_with_opcode;
    input [7:0] expected_opcode;
    integer timeout;
begin
    timeout = 0;
    $display("  Waiting for FWAIT (0x%02h) to start...", expected_opcode);

    while (!(starting_instruction && next_instruction_value.opcode == expected_opcode) && timeout < 100) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    if (starting_instruction && next_instruction_value.opcode == expected_opcode) begin
        $display("  FWAIT starting after %0d cycles", timeout);
    end else begin
        $display("  [WARN] Timeout waiting for FWAIT after %0d cycles", timeout);
    end
end
endtask

//============================================================================
// Main Test Sequence
//============================================================================

initial begin
    integer timeout;
    integer boot_cycles;
    integer i;

    // Initialize signals
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    clk = 0;
    reset = 1;
    nmi_pulse = 0;
    intr = 0;
    int_enabled = 0;
    stall = 0;
    divide_error = 0;
    rm_is_reg = 1;  // Register mode
    modrm_reg = 3'h0;
    zf = 0;
    tf = 0;
    jump_taken = 0;
    rb_zero = 0;
    fpu_busy = 0;
    fpu_int = 0;
    fifo_empty = 1;  // Start with empty FIFO
    fifo_resetting = 0;
    loop_done = 0;
    debug_seize = 0;
    debug_addr = 8'h00;
    debug_run = 0;

    // Initialize instruction
    create_instruction(8'h90, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);

    $display("======================================================================");
    $display("FPU FWAIT ERROR Pin Detection Test");
    $display("Minimal test following working microcode_tb pattern");
    $display("======================================================================");

    // Release reset
    $display("\n--- Reset Sequence ---");
    #100;
    reset = 0;
    $display("Reset released");

    // Monitor boot sequence
    boot_cycles = 0;
    for (i = 0; i < 200; i = i + 1) begin
        @(posedge clk);
        boot_cycles = boot_cycles + 1;

        // Break if we see starting_instruction (boot complete)
        if (starting_instruction) begin
            $display("Boot complete after %0d cycles!", boot_cycles);
            i = 200; // Exit loop
        end
    end

    if (!starting_instruction) begin
        $display("  WARNING: No starting_instruction seen after %0d cycles", boot_cycles);
    end

    #40;  // Settling time

    //========================================================================
    // Test 1: FWAIT completes when FPU not busy and no error
    //========================================================================
    $display("\n--- Test 1: FWAIT normal completion ---");
    $display("Setting up FWAIT instruction (0x9B)...");
    create_instruction(8'h9B, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);
    fifo_empty = 0;
    fpu_busy = 0;
    fpu_int = 0;
    $display("  FIFO: empty=%b opcode=0x%02h", fifo_empty, next_instruction_value.opcode);

    // Wait one clock for signals to settle
    @(posedge clk);
    $display("  [DEBUG] After 1 clock: start=%b next_micro=%b", starting_instruction, next_microinstruction);

    // Debug: Check what happens without opcode check
    $display("  [DEBUG] Checking if sequencer starts at all...");
    timeout = 0;
    while (!starting_instruction && timeout < 10) begin
        @(posedge clk);
        timeout = timeout + 1;
        $display("  [DEBUG] Cycle %0d: start=%b next_op=0x%02h fifo_empty=%b fifo_rd=%b next_instr=%b next_micro=%b",
                 timeout, starting_instruction, next_instruction_value.opcode, fifo_empty, fifo_rd_en,
                 next_instruction, next_microinstruction);
    end

    if (!starting_instruction) begin
        $display("  [ERROR] Sequencer never started! Aborting test.");
        $finish;
    end

    $display("  [DEBUG] Sequencer started after %0d cycles!", timeout);

    wait_for_instruction_start_with_opcode(8'h9B);

    // Wait for FIFO read and cur_instruction update
    @(posedge clk);  // FIFO read cycle
    @(posedge clk);  // cur_instruction updated

    $display("  Current opcode after start: 0x%02h", opcode);
    check_result(1'b1, opcode == 8'h9B, "FWAIT opcode correct");

    // FWAIT should complete quickly (1-2 microinstructions)
    timeout = 0;
    while (!next_instruction && timeout < 10) begin
        @(posedge clk);
        timeout = timeout + 1;
        $display("  Cycle %0d: busy=%b int=%b next=%b tmp_wr=%b imm=0x%04h",
                 timeout, fpu_busy, fpu_int, next_instruction, tmp_wr_en, microcode_immediate);
    end

    check_result(1'b1, next_instruction, "FWAIT completes normally");

    //========================================================================
    // Test 2: FWAIT polls while FPU busy
    //========================================================================
    $display("\n--- Test 2: FWAIT polling while FPU busy ---");
    fifo_empty = 0;
    fpu_busy = 1;  // FPU is busy
    fpu_int = 0;
    create_instruction(8'h9B, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);

    wait_for_instruction_start_with_opcode(8'h9B);

    @(posedge clk);
    @(posedge clk);

    $display("  Checking polling behavior...");

    // Should stay in polling loop
    repeat(5) @(posedge clk);
    check_result(1'b0, next_instruction, "FWAIT stays in busy loop");

    // Clear busy
    $display("  Clearing FPU busy...");
    fpu_busy = 0;

    // Should complete now
    timeout = 0;
    while (!next_instruction && timeout < 10) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    check_result(1'b1, next_instruction, "FWAIT completes after busy clears");

    //========================================================================
    // Test 3: FWAIT detects ERROR pin and triggers INT 16
    //========================================================================
    $display("\n--- Test 3: FWAIT ERROR pin detection ---");
    fifo_empty = 0;
    fpu_busy = 0;
    fpu_int = 1;  // FPU ERROR asserted!
    create_instruction(8'h9B, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);

    wait_for_instruction_start_with_opcode(8'h9B);

    @(posedge clk);
    @(posedge clk);

    $display("  Monitoring ERROR detection...");

    // FWAIT should detect error and prepare INT 16
    timeout = 0;
    while (!tmp_wr_en && timeout < 15) begin
        @(posedge clk);
        timeout = timeout + 1;
        $display("  Cycle %0d: busy=%b int=%b tmp_wr=%b imm=0x%04h",
                 timeout, fpu_busy, fpu_int, tmp_wr_en, microcode_immediate);
    end

    check_result(1'b1, tmp_wr_en, "TMP write enable asserted for INT vector");
    check_result(1'b1, microcode_immediate == 16'h10, "Immediate value is 0x10 (INT 16)");

    //========================================================================
    // Test Summary
    //========================================================================
    repeat(5) @(posedge clk);

    $display("\n======================================================================");
    $display("Test Summary");
    $display("======================================================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);

    if (fail_count == 0) begin
        $display("\n*** ALL TESTS PASSED! ***");
        $display("FPU ERROR pin polling via FWAIT validated!");
    end else begin
        $display("\n*** SOME TESTS FAILED ***");
    end
    $display("======================================================================\n");

    $finish;
end

//============================================================================
// Timeout
//============================================================================

initial begin
    #100000;  // 100 us timeout
    $display("\n*** TEST TIMEOUT ***\n");
    $finish;
end

//============================================================================
// VCD Dump
//============================================================================

initial begin
    $dumpfile("fpu_wait_minimal_tb.vcd");
    $dumpvars(0, fpu_wait_minimal_tb);
end

endmodule
