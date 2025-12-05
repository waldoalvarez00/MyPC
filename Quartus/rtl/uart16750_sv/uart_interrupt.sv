//
// UART interrupt control
//
// Author:   Sebastian Witt (original VHDL)
// Translator: Claude Code (SystemVerilog)
//
// This code is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.
//

module uart_interrupt (
    input  logic        CLK,        // Clock
    input  logic        RST,        // Reset
    input  logic [3:0]  IER,        // IER 3:0
    input  logic [4:0]  LSR,        // LSR 4:0
    input  logic        THI,        // Transmitter holding register empty interrupt
    input  logic        RDA,        // Receiver data available
    input  logic        CTI,        // Character timeout indication
    input  logic        AFE,        // Automatic flow control enable
    input  logic [3:0]  MSR,        // MSR 3:0
    output logic [3:0]  IIR,        // IIR 3:0
    output logic        INT         // Interrupt
);

    // Signals
    logic iRLSInterrupt;    // Receiver line status interrupt
    logic iRDAInterrupt;    // Received data available interrupt
    logic iCTIInterrupt;    // Character timeout indication interrupt
    logic iTHRInterrupt;    // Transmitter holding register empty interrupt
    logic iMSRInterrupt;    // Modem status interrupt
    logic [3:0] iIIR;       // IIR register

    // Priority 1: Receiver line status interrupt on: Overrun error, parity error, framing error or break interrupt
    assign iRLSInterrupt = IER[2] && (LSR[1] || LSR[2] || LSR[3] || LSR[4]);

    // Priority 2: Received data available or trigger level reached in FIFO mode
    assign iRDAInterrupt = IER[0] && RDA;

    // Priority 2: Character timeout indication
    assign iCTIInterrupt = IER[0] && CTI;

    // Priority 3: Transmitter holding register empty
    assign iTHRInterrupt = IER[1] && THI;

    // Priority 4: Modem status interrupt: dCTS (when AFC is disabled), dDSR, TERI, dDCD
    assign iMSRInterrupt = IER[3] && ((MSR[0] && !AFE) || MSR[1] || MSR[2] || MSR[3]);

    // IIR register
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iIIR <= 4'b0001;    // No interrupt pending
        end else begin
            if (iRLSInterrupt)
                iIIR <= 4'b0110;        // Receiver line status
            else if (iCTIInterrupt)
                iIIR <= 4'b1100;        // Character timeout indication
            else if (iRDAInterrupt)
                iIIR <= 4'b0100;        // Received data available
            else if (iTHRInterrupt)
                iIIR <= 4'b0010;        // THR empty
            else if (iMSRInterrupt)
                iIIR <= 4'b0000;        // Modem status
            else
                iIIR <= 4'b0001;        // No interrupt pending
        end
    end

    // Outputs
    assign IIR = iIIR;
    assign INT = ~iIIR[0];      // Interrupt active when bit 0 is 0

endmodule
