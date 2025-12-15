//
// UART transmitter
//
// Author:   Sebastian Witt (original VHDL)
// Translator: Claude AI (VHDL to SystemVerilog)
// Date:     27.01.2008 (original)
// Version:  1.0
//
// This code is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.

`default_nettype none

module uart_transmitter (
    input  logic       CLK,         // Clock
    input  logic       RST,         // Reset
    input  logic       TXCLK,       // Transmitter clock (2x baudrate)
    input  logic       TXSTART,     // Start transmitter
    input  logic       CLEAR,       // Clear transmitter state
    input  logic [1:0] WLS,         // Word length select
    input  logic       STB,         // Number of stop bits
    input  logic       PEN,         // Parity enable
    input  logic       EPS,         // Even parity select
    input  logic       SP,          // Stick parity
    input  logic       BC,          // Break control
    input  logic [7:0] DIN,         // Input data
    output logic       TXFINISHED,  // Transmitter operation finished
    output logic       SOUT         // Transmitter output
);

    // FSM states
    typedef enum logic [3:0] {
        IDLE, START, BIT0, BIT1, BIT2, BIT3, BIT4, BIT5, BIT6, BIT7, PAR, STOP, STOP2
    } state_type;

    state_type CState, NState;

    // Internal signals
    logic iTx2;         // Next TX step
    logic iSout;        // Transmitter output
    logic iParity;      // Parity
    logic iFinished;    // TX finished

    // Transmitter FSM update process
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            CState <= IDLE;
            iTx2   <= 1'b0;
        end else begin
            if (TXCLK) begin            // TX clock
                if (!iTx2) begin        // Two TX clocks per step
                    CState <= NState;   // Next step
                    iTx2   <= 1'b1;
                end else begin
                    if ((WLS == 2'b00) && STB && (CState == STOP2)) begin
                        CState <= NState;   // 1.5 stop bits for 5 bit word mode
                        iTx2   <= 1'b1;
                    end else begin
                        CState <= CState;   // First TX clock, wait
                        iTx2   <= 1'b0;
                    end
                end
            end
        end
    end

    // Transmitter FSM
    always_comb begin
        // Defaults
        NState = IDLE;
        iSout  = 1'b1;

        case (CState)
            IDLE:   if (TXSTART) NState = START;
            START:  begin
                        iSout = 1'b0;
                        NState = BIT0;
                    end
            BIT0:   begin
                        iSout = DIN[0];
                        NState = BIT1;
                    end
            BIT1:   begin
                        iSout = DIN[1];
                        NState = BIT2;
                    end
            BIT2:   begin
                        iSout = DIN[2];
                        NState = BIT3;
                    end
            BIT3:   begin
                        iSout = DIN[3];
                        NState = BIT4;
                    end
            BIT4:   begin
                        iSout = DIN[4];
                        if (WLS == 2'b00) begin        // 5 bits
                            if (PEN) NState = PAR;
                            else NState = STOP;
                        end else begin
                            NState = BIT5;
                        end
                    end
            BIT5:   begin
                        iSout = DIN[5];
                        if (WLS == 2'b01) begin        // 6 bits
                            if (PEN) NState = PAR;
                            else NState = STOP;
                        end else begin
                            NState = BIT6;
                        end
                    end
            BIT6:   begin
                        iSout = DIN[6];
                        if (WLS == 2'b10) begin        // 7 bits
                            if (PEN) NState = PAR;
                            else NState = STOP;
                        end else begin
                            NState = BIT7;
                        end
                    end
            BIT7:   begin
                        iSout = DIN[7];
                        if (PEN) NState = PAR;
                        else NState = STOP;
                    end
            PAR:    begin
                        if (SP) begin                   // Sticky parity
                            iSout = EPS ? 1'b0 : 1'b1;
                        end else begin
                            iSout = EPS ? iParity : ~iParity;
                        end
                        NState = STOP;
                    end
            STOP:   begin
                        if (STB) begin                  // 2 stop bits
                            NState = STOP2;
                        end else if (TXSTART) begin     // Next transmission
                            NState = START;
                        end
                    end
            STOP2:  if (TXSTART) NState = START;
            default: NState = IDLE;
        endcase
    end

    // Parity generation
    always_comb begin
        logic iP40, iP50, iP60, iP70;

        iP40 = DIN[4] ^ DIN[3] ^ DIN[2] ^ DIN[1] ^ DIN[0];
        iP50 = DIN[5] ^ iP40;
        iP60 = DIN[6] ^ iP50;
        iP70 = DIN[7] ^ iP60;

        case (WLS)
            2'b00:   iParity = iP40;
            2'b01:   iParity = iP50;
            2'b10:   iParity = iP60;
            default: iParity = iP70;
        endcase
    end

    // Signal TX finished on STOP bit transmission
    logic iLast;

    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iFinished <= 1'b0;
            iLast <= 1'b0;
        end else begin
            iFinished <= 1'b0;
            if (!iLast && (CState == STOP)) begin
                iFinished <= 1'b1;
            end

            iLast <= (CState == STOP);
        end
    end

    // Output signals
    assign SOUT       = BC ? 1'b0 : iSout;
    assign TXFINISHED = iFinished;

endmodule

`default_nettype wire
