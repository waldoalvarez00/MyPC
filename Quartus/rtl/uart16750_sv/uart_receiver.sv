//
// UART receiver
//
// Author:   Sebastian Witt (original VHDL)
// Translator: Claude Code (SystemVerilog)
// Date:     27.01.2008 (original)
// Version:  1.1
//
// This code is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.
//
// This code is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License along with this library; if not, write to the
// Free Software  Foundation, Inc., 59 Temple Place, Suite 330,
// Boston, MA  02111-1307  USA
//

module uart_receiver (
    input  logic        CLK,            // Clock
    input  logic        RST,            // Reset
    input  logic        RXCLK,          // Receiver clock (16x baudrate)
    input  logic        RXCLEAR,        // Reset receiver state
    input  logic [1:0]  WLS,            // Word length select
    input  logic        STB,            // Number of stop bits
    input  logic        PEN,            // Parity enable
    input  logic        EPS,            // Even parity select
    input  logic        SP,             // Stick parity
    input  logic        SIN,            // Receiver input
    output logic        PE,             // Parity error
    output logic        FE,             // Framing error
    output logic        BI,             // Break interrupt
    output logic [7:0]  DOUT,           // Output data
    output logic        RXFINISHED      // Receiver operation finished
);

    // FSM states
    typedef enum logic [2:0] {
        IDLE  = 3'd0,
        START = 3'd1,
        DATA  = 3'd2,
        PAR   = 3'd3,
        STOP  = 3'd4,
        MWAIT = 3'd5
    } state_t;

    state_t CState, NState;

    // Signals
    logic        iBaudCountClear;       // Baud counter clear
    logic        iBaudStep;             // Next symbol pulse
    logic        iBaudStepD;            // Next symbol pulse delayed by one clock
    logic        iFilterClear;          // Reset input filter
    logic        iFSIN;                 // Filtered SIN
    logic        iParity;               // Data parity
    logic        iParityReceived;       // Parity received
    logic [3:0]  iDataCount;            // Data bit counter
    logic        iDataCountInit;        // Initialize data bit counter to word length
    logic        iDataCountFinish;      // Data bit counter finished
    logic        iRXFinished;           // Word received, output data valid
    logic        iFE;                   // Internal frame error
    logic        iBI;                   // Internal break interrupt
    logic        iNoStopReceived;       // No valid stop bit received
    logic [7:0]  iDOUT;                 // Data output

    // Baudrate counter: RXCLK/16
    slib_counter #(
        .WIDTH(4)
    ) RX_BRC (
        .CLK      (CLK),
        .RST      (RST),
        .CLEAR    (iBaudCountClear),
        .LOAD     (1'b0),
        .ENABLE   (RXCLK),
        .DOWN     (1'b0),
        .D        (4'h0),
        .Q        (),
        .OVERFLOW (iBaudStep)
    );

    // Input filter
    slib_mv_filter #(
        .WIDTH     (4),
        .THRESHOLD (10)
    ) RX_MVF (
        .CLK    (CLK),
        .RST    (RST),
        .SAMPLE (RXCLK),
        .CLEAR  (iFilterClear),
        .D      (SIN),
        .Q      (iFSIN)
    );

    // iBaudStepD - delay iBaudStep by one clock
    always_ff @(posedge CLK or posedge RST) begin
        if (RST)
            iBaudStepD <= 1'b0;
        else
            iBaudStepD <= iBaudStep;
    end

    assign iFilterClear = iBaudStepD | iBaudCountClear;

    // Parity generation
    assign iParity = iDOUT[7] ^ iDOUT[6] ^ iDOUT[5] ^ iDOUT[4] ^
                     iDOUT[3] ^ iDOUT[2] ^ iDOUT[1] ^ iDOUT[0] ^ ~EPS;

    // Data bit capture
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iDataCount <= 4'd0;
            iDOUT      <= 8'd0;
        end else begin
            if (iDataCountInit) begin
                iDataCount <= 4'd0;
                iDOUT      <= 8'd0;
            end else begin
                if (iBaudStep && !iDataCountFinish) begin
                    iDOUT[iDataCount[2:0]] <= iFSIN;
                    iDataCount <= iDataCount + 1'b1;
                end
            end
        end
    end

    // Data count finish detection
    assign iDataCountFinish = (WLS == 2'b00 && iDataCount == 4'd5) ||
                              (WLS == 2'b01 && iDataCount == 4'd6) ||
                              (WLS == 2'b10 && iDataCount == 4'd7) ||
                              (WLS == 2'b11 && iDataCount == 4'd8);

    // FSM update process
    always_ff @(posedge CLK or posedge RST) begin
        if (RST)
            CState <= IDLE;
        else
            CState <= NState;
    end

    // RX FSM - next state and output logic
    always_comb begin
        // Defaults
        NState          = IDLE;
        iBaudCountClear = 1'b0;
        iDataCountInit  = 1'b0;
        iRXFinished     = 1'b0;

        case (CState)
            IDLE: begin
                if (!SIN) begin                 // Start detected
                    NState = START;
                end
                iBaudCountClear = 1'b1;
                iDataCountInit  = 1'b1;
            end

            START: begin
                iDataCountInit = 1'b1;
                if (iBaudStep) begin            // Wait for start bit end
                    if (!iFSIN) begin
                        NState = DATA;
                    end
                end else begin
                    NState = START;
                end
            end

            DATA: begin
                if (iDataCountFinish) begin     // Received all data bits
                    if (PEN)
                        NState = PAR;           // Parity enabled
                    else
                        NState = STOP;          // No parity
                end else begin
                    NState = DATA;
                end
            end

            PAR: begin
                if (iBaudStep)                  // Wait for parity bit
                    NState = STOP;
                else
                    NState = PAR;
            end

            STOP: begin
                if (iBaudStep) begin            // Wait for stop bit
                    if (!iFSIN) begin           // No stop bit received
                        iRXFinished = 1'b1;
                        NState = MWAIT;
                    end else begin
                        iRXFinished = 1'b1;
                        NState = IDLE;          // Stop bit end
                    end
                end else begin
                    NState = STOP;
                end
            end

            MWAIT: begin
                if (!SIN) begin                 // Wait for mark
                    NState = MWAIT;
                end
            end

            default: NState = IDLE;
        endcase
    end

    // Check parity
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            PE              <= 1'b0;
            iParityReceived <= 1'b0;
        end else begin
            if (CState == PAR && iBaudStep) begin
                iParityReceived <= iFSIN;       // Received parity bit
            end

            // Check parity
            if (PEN) begin                      // Parity enabled
                PE <= 1'b0;
                if (SP) begin                   // Sticky parity
                    if ((EPS ^ iParityReceived) == 1'b0)
                        PE <= 1'b1;             // Parity error
                end else begin
                    if (iParity != iParityReceived)
                        PE <= 1'b1;             // Parity error
                end
            end else begin
                PE              <= 1'b0;        // Parity disabled
                iParityReceived <= 1'b0;
            end
        end
    end

    // Framing error and break interrupt
    assign iNoStopReceived = !iFSIN && (CState == STOP);
    assign iBI = (iDOUT == 8'h00) && !iParityReceived && iNoStopReceived;
    assign iFE = iNoStopReceived;

    // Output signals
    assign DOUT       = iDOUT;
    assign BI         = iBI;
    assign FE         = iFE;
    assign RXFINISHED = iRXFinished;

endmodule
