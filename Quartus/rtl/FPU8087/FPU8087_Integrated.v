`timescale 1ns / 1ps

//=====================================================================
// Integrated FPU8087 Module
//
// Combines the FPU_CPU_Interface and FPU_Core_Wrapper to create
// a complete FPU that can communicate with the CPU.
//=====================================================================

module FPU8087_Integrated(
    // Clock and Reset
    input wire clk,
    input wire reset,

    // ========== CPU Side Interface ==========

    // Instruction Interface
    input wire        cpu_fpu_instr_valid,
    input wire [7:0]  cpu_fpu_opcode,
    input wire [7:0]  cpu_fpu_modrm,
    output wire       cpu_fpu_instr_ack,

    // Data Transfer Interface
    input wire        cpu_fpu_data_write,
    input wire        cpu_fpu_data_read,
    input wire [2:0]  cpu_fpu_data_size,
    input wire [79:0] cpu_fpu_data_in,
    output wire [79:0] cpu_fpu_data_out,
    output wire       cpu_fpu_data_ready,

    // Status and Control
    output wire       cpu_fpu_busy,
    output wire [15:0] cpu_fpu_status_word,
    input wire [15:0] cpu_fpu_control_word,
    input wire        cpu_fpu_ctrl_write,
    output wire       cpu_fpu_exception,
    output wire       cpu_fpu_irq,

    // Synchronization
    input wire        cpu_fpu_wait,
    output wire       cpu_fpu_ready
);

    //=================================================================
    // Interface to Core Signals
    //=================================================================

    wire        if_fpu_start;
    wire [7:0]  if_fpu_operation;
    wire [7:0]  if_fpu_operand_select;
    wire [79:0] if_fpu_operand_data;
    wire        if_fpu_operation_complete;
    wire [79:0] if_fpu_result_data;
    wire [15:0] if_fpu_status;
    wire        if_fpu_error;
    wire [15:0] if_fpu_control_reg;
    wire        if_fpu_control_update;

    //=================================================================
    // FPU Interface Module
    //=================================================================

    FPU_CPU_Interface interface (
        .clk(clk),
        .reset(reset),

        // CPU Side
        .cpu_fpu_instr_valid(cpu_fpu_instr_valid),
        .cpu_fpu_opcode(cpu_fpu_opcode),
        .cpu_fpu_modrm(cpu_fpu_modrm),
        .cpu_fpu_instr_ack(cpu_fpu_instr_ack),

        .cpu_fpu_data_write(cpu_fpu_data_write),
        .cpu_fpu_data_read(cpu_fpu_data_read),
        .cpu_fpu_data_size(cpu_fpu_data_size),
        .cpu_fpu_data_in(cpu_fpu_data_in),
        .cpu_fpu_data_out(cpu_fpu_data_out),
        .cpu_fpu_data_ready(cpu_fpu_data_ready),

        .cpu_fpu_busy(cpu_fpu_busy),
        .cpu_fpu_status_word(cpu_fpu_status_word),
        .cpu_fpu_control_word(cpu_fpu_control_word),
        .cpu_fpu_ctrl_write(cpu_fpu_ctrl_write),
        .cpu_fpu_exception(cpu_fpu_exception),
        .cpu_fpu_irq(cpu_fpu_irq),

        .cpu_fpu_wait(cpu_fpu_wait),
        .cpu_fpu_ready(cpu_fpu_ready),

        // FPU Core Side
        .fpu_start(if_fpu_start),
        .fpu_operation(if_fpu_operation),
        .fpu_operand_select(if_fpu_operand_select),
        .fpu_operand_data(if_fpu_operand_data),

        .fpu_operation_complete(if_fpu_operation_complete),
        .fpu_result_data(if_fpu_result_data),
        .fpu_status(if_fpu_status),
        .fpu_error(if_fpu_error),

        .fpu_control_reg(if_fpu_control_reg),
        .fpu_control_update(if_fpu_control_update)
    );

    //=================================================================
    // FPU Core Wrapper
    //=================================================================

    FPU_Core_Wrapper core (
        .clk(clk),
        .reset(reset),

        .if_start(if_fpu_start),
        .if_operation(if_fpu_operation),
        .if_operand_select(if_fpu_operand_select),
        .if_operand_data(if_fpu_operand_data),

        .if_operation_complete(if_fpu_operation_complete),
        .if_result_data(if_fpu_result_data),
        .if_status(if_fpu_status),
        .if_error(if_fpu_error),

        .if_control_reg(if_fpu_control_reg),
        .if_control_update(if_fpu_control_update)
    );

endmodule
