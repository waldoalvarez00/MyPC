/**
 * Debug test to trace microcode address progression for FWAIT
 */

`timescale 1ns/1ps

`include "../Quartus/rtl/CPU/RegisterEnum.sv"
`include "../Quartus/rtl/CPU/MicrocodeTypes.sv"
`include "../Quartus/rtl/CPU/Instruction.sv"

module fpu_wait_debug_tb;

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

// Monitor to trace address progression
always @(posedge clk) begin
    if (!reset) begin
        $display("T=%0t addr=0x%03h next_addr=0x%03h start=%b next_i=%b fifo_empty=%b opcode_in=0x%02h jump_type=%0d",
                 $time, dut.addr, dut.next_addr, starting_instruction, next_instruction,
                 fifo_empty, next_instruction_value.opcode, dut.current.jump_type);
    end
end

initial begin
    integer timeout;

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

    create_instruction(8'h9B, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);

    $display("=== FWAIT Address Trace Test ===");
    $display("Watching for addr to reach 0x100 (next_instruction), then 0x9B (FWAIT opcode)");

    // Reset
    #100;
    reset = 0;
    $display("\nReset released at T=%0t", $time);

    // Watch for next_instruction_address
    timeout = 0;
    while (dut.addr != 11'h100 && timeout < 100) begin
        @(posedge clk);
        timeout = timeout + 1;
    end

    if (dut.addr == 11'h100) begin
        $display("\n*** Reached next_instruction_address (0x100) after %0d cycles ***", timeout);

        // Now provide FWAIT instruction
        fifo_empty = 0;
        create_instruction(8'h9B, 1'b0, 1'b0, REP_PREFIX_NONE, 1'b0);
        $display("Injected FWAIT (0x9B) into FIFO");

        // Watch what happens
        repeat(20) @(posedge clk);

    end else begin
        $display("\n*** ERROR: Never reached next_instruction_address! ***");
    end

    $finish;
end

initial begin
    #50000;
    $display("\n*** TIMEOUT ***\n");
    $finish;
end

initial begin
    $dumpfile("fpu_wait_debug_tb.vcd");
    $dumpvars(0, fpu_wait_debug_tb);
end

endmodule
