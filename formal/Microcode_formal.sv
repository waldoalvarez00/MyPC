// Formal harness for Quartus/rtl/CPU/Microcode.sv

`default_nettype none

module Microcode_formal(
    input clk
);
    // Clock and reset
    reg reset;

    // Interrupt and control inputs
    (* anyseq *) reg nmi_pulse;
    (* anyseq *) reg intr;
    (* anyseq *) reg stall;
    (* anyseq *) reg divide_error;
    (* anyseq *) reg rm_is_reg;
    (* anyseq *) reg [2:0] modrm_reg;
    (* anyseq *) reg int_enabled;
    (* anyseq *) reg zf;
    (* anyseq *) reg tf;
    (* anyseq *) reg jump_taken;
    (* anyseq *) reg rb_zero;
    (* anyseq *) reg fpu_busy;

    // FIFO / loop / debug inputs
    (* anyseq *) reg fifo_empty;
    (* anyseq *) reg fifo_resetting;
    (* anyseq *) reg loop_done;
    (* anyseq *) reg debug_seize;
    (* anyseq *) reg [7:0] debug_addr;
    (* anyseq *) reg debug_run;

    // Instruction stream
    (* anyseq *) Instruction next_instruction_value;
    wire        fifo_rd_en;
    Instruction cur_instruction;

    // Outputs we don’t directly constrain, but wire for completeness
    wire        inta;
    wire        irq_to_mdr;
    wire        start_interrupt;
    wire        do_escape_fault;
    wire        starting_instruction;
    wire [15:0] microcode_immediate;
    wire [8:0]  update_flags;
    wire        modrm_start;
    wire        use_microcode_immediate;
    wire [7:0]  opcode;
    wire        lock;
    wire        multibit_shift;
    wire        is_hlt;
    wire        next_microinstruction;
    wire [2:0]  a_sel;
    wire [5:0]  alu_op;
    wire [2:0]  b_sel;
    wire        ext_int_yield;
    wire        io;
    wire        load_ip;
    wire        mar_wr_sel;
    wire        mar_write;
    wire        mdr_write;
    wire        mem_read;
    wire        mem_write;
    wire        next_instruction;
    wire        ra_modrm_rm_reg;
    wire [2:0]  ra_sel;
    wire        rb_cl;
    wire [2:0]  rd_sel;
    wire [1:0]  rd_sel_source;
    wire [1:0]  reg_wr_source;
    wire [1:0]  segment;
    wire        segment_force;
    wire        segment_wr_en;
    wire        tmp_wr_en;
    wire        tmp_wr_sel;
    wire        fpu_ctrl_wr;
    wire        width;
    wire        reg_wr_en;
    wire        loop_next;
    wire        debug_stopped;

    // DUT
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

    // Basic reset: start in reset, then release
    initial reset = 1'b1;

    reg seen_reset;

    always @(posedge clk) begin
        if ($initstate) begin
            reset      <= 1'b1;
            seen_reset <= 1'b0;
        end else begin
            reset      <= 1'b0;
            if (reset)
                seen_reset <= 1'b1;
        end
    end

    // Environment assumptions (very light):
    always @(posedge clk) if (seen_reset && !reset) begin
        // If the microcode asks to read a new instruction, assume the FIFO
        // is not empty. This reflects a sane interface contract with Prefetch.
        if (fifo_rd_en)
            assume(!fifo_empty);
    end

    // Safety properties
    always @(posedge clk) if (seen_reset && !reset) begin
        // FIFO read-enable must match starting_instruction (as wired in RTL).
        assert(fifo_rd_en == starting_instruction);

        // Never attempt to write both a segment register and a general register
        // in the same microinstruction.
        assert(!(reg_wr_en && segment_wr_en));
    end

endmodule

