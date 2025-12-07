//
// GameBoy Color Sound Module Stub
//
// This is a placeholder module for the gbc_snd VHDL module.
// It provides silent audio output for initial testing.
// Replace with proper sound implementation later.
//
// Copyright (c) 2024 - MIT License
//

module gbc_snd (
    input         clk,
    input         ce,
    input         reset,

    input         is_gbc,
    input         remove_pops,

    // CPU interface
    input         s1_read,
    input         s1_write,
    input  [6:0]  s1_addr,
    output [7:0]  s1_readdata,
    input  [7:0]  s1_writedata,

    // Audio output
    output [15:0] snd_left,
    output [15:0] snd_right,

    // Savestate interface (stubbed)
    input  [63:0] SaveStateBus_Din,
    input  [9:0]  SaveStateBus_Adr,
    input         SaveStateBus_wren,
    input         SaveStateBus_rst,
    output [63:0] SaveStateBus_Dout
);

    // Audio output registers (simple stub - just implement basic register read)
    reg [7:0] audio_regs [0:127];  // Audio registers at FF10-FF3F

    // Register read
    assign s1_readdata = audio_regs[s1_addr];

    // Silent audio output
    assign snd_left  = 16'h0000;
    assign snd_right = 16'h0000;

    // Savestate stub
    assign SaveStateBus_Dout = 64'h0;

    // Register write
    integer i;
    always @(posedge clk) begin
        if (reset) begin
            for (i = 0; i < 128; i = i + 1) begin
                audio_regs[i] <= 8'h00;
            end
            // Initialize NR52 (FF26) to indicate sound off
            audio_regs[7'h26] <= 8'h00;
        end
        else if (ce && s1_write) begin
            audio_regs[s1_addr] <= s1_writedata;
        end
    end

endmodule
