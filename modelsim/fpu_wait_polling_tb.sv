/**
 * Comprehensive FWAIT polling test
 * Tests FPU BUSY polling and ERROR pin detection
 */

`timescale 1ns/1ps

`include "../Quartus/rtl/CPU/RegisterEnum.sv"
`include "../Quartus/rtl/CPU/MicrocodeTypes.sv"
`include "../Quartus/rtl/CPU/Instruction.sv"

module fpu_wait_polling_tb;

reg clk;
reg reset;

// Input signals
reg nmi_pulse;
reg intr;
reg int_enabled;
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
reg fifo_empty;
reg fifo_resetting;
reg loop_done;
reg debug_seize;
reg [7:0] debug_addr;
reg debug_run;

// Output signals
wire inta;
wire irq_to_mdr;
wire start_interrupt;
wire do_escape_fault;
wire starting_instruction;
wire [15:0] microcode_immediate;
wire [8:0] update_flags;
wire modrm_start;
wire use_microcode_immediate;
wire [7:0] opcode;
wire lock;
wire multibit_shift;
wire is_hlt;
wire next_microinstruction;
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
wire fifo_rd_en;
wire loop_next;
wire debug_stopped;

Instruction next_instruction_value;
Instruction cur_instruction;

integer test_passed;
integer test_failed;

always #5 clk = ~clk;

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

initial begin
    $readmemb("microcode.bin", dut.mem);
end

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
    next_instruction_value.mod_rm = 8'hc0;
    next_instruction_value.displacement = 16'h0000;
    next_instruction_value.immediates[0] = 16'h1234;
    next_instruction_value.immediates[1] = 16'h5678;
    next_instruction_value.length = 4'd1;
end
endtask

task wait_for_next_instruction_address;
    integer timeout;
begin
    timeout = 0;
    while (dut.addr != 11'h100 && timeout < 100) begin
        @(posedge clk);
        timeout = timeout + 1;
    end
    if (dut.addr != 11'h100) begin
        $display("  ERROR: Never reached next_instruction_address");
        test_failed = test_failed + 1;
    end
end
endtask

task inject_fwait;
begin
    fifo_empty = 0;
    create_instruction(8'h9B, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);
end
endtask

task clear_fifo;
begin
    fifo_empty = 1;
end
endtask

initial begin
    integer timeout;
    integer poll_count;

    // Initialize
    clk = 0;
    reset = 1;
    nmi_pulse = 0;
    intr = 0;
    int_enabled = 0;
    stall = 0;
    divide_error = 0;
    rm_is_reg = 1;
    modrm_reg = 3'h0;
    zf = 0;
    tf = 0;
    jump_taken = 0;
    rb_zero = 0;
    fpu_busy = 0;
    fpu_int = 0;
    fifo_empty = 1;
    fifo_resetting = 0;
    loop_done = 0;
    debug_seize = 0;
    debug_addr = 8'h00;
    debug_run = 0;

    test_passed = 0;
    test_failed = 0;

    create_instruction(8'h9B, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);

    $display("======================================================================");
    $display("FPU FWAIT Polling Test Suite");
    $display("Tests BUSY polling and ERROR pin detection");
    $display("======================================================================\n");

    // Reset
    #100;
    reset = 0;
    $display("Reset released\n");

    // ==========================================
    // Test 1: FPU not busy, no error - immediate completion
    // ==========================================
    $display("=== Test 1: FWAIT with FPU ready (not busy, no error) ===");
    wait_for_next_instruction_address;

    fpu_busy = 0;
    fpu_int = 0;
    inject_fwait;

    // Wait for instruction to start and complete
    timeout = 0;
    while (!next_instruction && timeout < 20) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    if (next_instruction) begin
        $display("  PASS: FWAIT completed immediately when FPU ready (cycles=%0d)\n", timeout);
        test_passed = test_passed + 1;
    end else begin
        $display("  FAIL: FWAIT did not complete\n");
        test_failed = test_failed + 1;
    end

    clear_fifo;
    @(posedge clk);
    @(posedge clk);

    // ==========================================
    // Test 2: FPU busy, then clears - polling behavior
    // ==========================================
    $display("=== Test 2: FWAIT with FPU initially busy ===");
    wait_for_next_instruction_address;

    fpu_busy = 1;  // FPU is busy
    fpu_int = 0;
    inject_fwait;

    // Wait for instruction to start
    timeout = 0;
    while (!starting_instruction && timeout < 20) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    if (!starting_instruction) begin
        $display("  FAIL: FWAIT never started\n");
        test_failed = test_failed + 1;
    end else begin
        // FWAIT should poll the busy pin
        $display("  FWAIT started, polling FPU BUSY...");
        poll_count = 0;

        // Let it poll for a few cycles
        repeat(5) begin
            @(posedge clk);
            if (dut.addr != 11'h100 && !next_instruction) begin
                poll_count = poll_count + 1;
            end
        end

        // Clear FPU busy
        fpu_busy = 0;
        $display("  Cleared FPU BUSY after %0d poll cycles", poll_count);

        // Should complete now
        timeout = 0;
        while (!next_instruction && timeout < 20) begin
            @(posedge clk);
            timeout = timeout + 1;
        end

        if (next_instruction && poll_count > 0) begin
            $display("  PASS: FWAIT polled BUSY pin and completed after busy cleared\n");
            test_passed = test_passed + 1;
        end else if (poll_count == 0) begin
            $display("  FAIL: FWAIT didn't poll BUSY pin\n");
            test_failed = test_failed + 1;
        end else begin
            $display("  FAIL: FWAIT didn't complete after busy cleared\n");
            test_failed = test_failed + 1;
        end
    end

    clear_fifo;
    @(posedge clk);
    @(posedge clk);

    // ==========================================
    // Test 3: FPU ERROR pin asserted - should trigger INT 16
    // ==========================================
    $display("=== Test 3: FWAIT with ERROR pin asserted ===");
    wait_for_next_instruction_address;

    fpu_busy = 0;
    fpu_int = 1;  // ERROR pin asserted
    inject_fwait;

    // Wait for instruction to start
    timeout = 0;
    while (!starting_instruction && timeout < 20) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    if (!starting_instruction) begin
        $display("  FAIL: FWAIT never started\n");
        test_failed = test_failed + 1;
    end else begin
        // Should detect error and prepare INT 16
        $display("  FWAIT started, checking ERROR pin...");

        timeout = 0;
        while (!tmp_wr_en && timeout < 20) begin
            @(posedge clk);
            timeout = timeout + 1;
        end

        if (tmp_wr_en && microcode_immediate == 16'h10) begin
            $display("  PASS: ERROR detected, INT 16 (0x10) triggered\n");
            test_passed = test_passed + 1;
        end else if (tmp_wr_en) begin
            $display("  FAIL: Wrong interrupt vector: 0x%04h (expected 0x10)\n", microcode_immediate);
            test_failed = test_failed + 1;
        end else begin
            $display("  FAIL: ERROR not detected or INT not triggered\n");
            test_failed = test_failed + 1;
        end
    end

    // ==========================================
    // Summary
    // ==========================================
    $display("======================================================================");
    $display("Test Results:");
    $display("  PASSED: %0d", test_passed);
    $display("  FAILED: %0d", test_failed);
    if (test_failed == 0) begin
        $display("\n*** ALL TESTS PASSED ***\n");
    end else begin
        $display("\n*** SOME TESTS FAILED ***\n");
    end
    $display("======================================================================");

    $finish;
end

initial begin
    #100000;
    $display("\n*** TIMEOUT ***\n");
    $finish;
end

initial begin
    $dumpfile("fpu_wait_polling_tb.vcd");
    $dumpvars(0, fpu_wait_polling_tb);
end

endmodule
