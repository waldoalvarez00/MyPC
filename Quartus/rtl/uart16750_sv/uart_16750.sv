//
// UART 16750 - Full Implementation
//
// Author:   Sebastian Witt (original VHDL)
// Translator: Claude Code (SystemVerilog)
// Date:     29.01.2008 (original)
// Version:  1.4
//
// History:  1.0 - Initial version
//           1.1 - THR empty interrupt register connected to RST
//           1.2 - Registered outputs
//           1.3 - Automatic flow control
//           1.4 - De-assert IIR FIFO64 when FIFO is disabled
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

module uart_16750 (
    input  logic        CLK,            // Clock
    input  logic        RST,            // Reset
    input  logic        BAUDCE,         // Baudrate generator clock enable
    input  logic        CS,             // Chip select
    input  logic        WR,             // Write to UART
    input  logic        RD,             // Read from UART
    input  logic [2:0]  A,              // Register select
    input  logic [7:0]  DIN,            // Data bus input
    output logic [7:0]  DOUT,           // Data bus output
    output logic        DDIS,           // Driver disable
    output logic        INT,            // Interrupt output
    output logic        OUT1N,          // Output 1
    output logic        OUT2N,          // Output 2
    input  logic        RCLK,           // Receiver clock (16x baudrate)
    output logic        BAUDOUTN,       // Baudrate generator output (16x baudrate)
    output logic        RTSN,           // RTS output
    output logic        DTRN,           // DTR output
    input  logic        CTSN,           // CTS input
    input  logic        DSRN,           // DSR input
    input  logic        DCDN,           // DCD input
    input  logic        RIN,            // RI input
    input  logic        SIN,            // Receiver input
    output logic        SOUT            // Transmitter output
);

    // ================================================================
    // Internal signals
    // ================================================================

    // Global device signals
    logic iCSWR;                        // Chipselect and write
    logic iCSRD;                        // Chipselect and read
    logic iWriteFE;                     // Write falling edge
    logic iReadFE;                      // Read falling edge
    logic iWrite;                       // Write to UART
    logic iRead;                        // Read from UART
    logic [2:0] iA;                     // UART register address
    logic [7:0] iDIN;                   // UART data input

    // UART registers read/write signals
    logic iRBRRead;                     // Read from RBR
    logic iTHRWrite;                    // Write to THR
    logic iDLLWrite;                    // Write to DLL
    logic iDLMWrite;                    // Write to DLM
    logic iIERWrite;                    // Write to IER
    logic iIIRRead;                     // Read from IIR
    logic iFCRWrite;                    // Write to FCR
    logic iLCRWrite;                    // Write to LCR
    logic iMCRWrite;                    // Write to MCR
    logic iLSRRead;                     // Read from LSR
    logic iMSRRead;                     // Read from MSR
    logic iSCRWrite;                    // Write to SCR

    // UART registers
    logic [7:0] iTSR;                   // Transmitter holding register
    logic [7:0] iRBR;                   // Receiver buffer register
    logic [7:0] iDLL;                   // Divisor latch LSB
    logic [7:0] iDLM;                   // Divisor latch MSB
    logic [7:0] iIER;                   // Interrupt enable register
    logic [7:0] iIIR;                   // Interrupt identification register
    logic [7:0] iLCR;                   // Line control register
    logic [7:0] iMCR;                   // Modem control register
    logic [7:0] iLSR;                   // Line status register
    logic [7:0] iMSR;                   // Modem status register
    logic [7:0] iSCR;                   // Scratch register

    // FCR register signals
    logic iFCR_FIFOEnable;              // FCR: FIFO enable
    logic iFCR_RXFIFOReset;             // FCR: Receiver FIFO reset
    logic iFCR_TXFIFOReset;             // FCR: Transmitter FIFO reset
    logic iFCR_DMAMode;                 // FCR: DMA mode select
    logic iFCR_FIFO64E;                 // FCR: 64 byte FIFO enable
    logic [1:0] iFCR_RXTrigger;         // FCR: Receiver trigger

    // LCR register signals
    logic [1:0] iLCR_WLS;               // LCR: Word length select
    logic iLCR_STB;                     // LCR: Number of stop bits
    logic iLCR_PEN;                     // LCR: Parity enable
    logic iLCR_EPS;                     // LCR: Even parity select
    logic iLCR_SP;                      // LCR: Sticky parity
    logic iLCR_BC;                      // LCR: Break control
    logic iLCR_DLAB;                    // LCR: Divisor latch access bit

    // MCR register signals
    logic iMCR_DTR;                     // MCR: Data terminal ready
    logic iMCR_RTS;                     // MCR: Request to send
    logic iMCR_OUT1;                    // MCR: OUT1
    logic iMCR_OUT2;                    // MCR: OUT2
    logic iMCR_LOOP;                    // MCR: Loop
    logic iMCR_AFE;                     // MCR: Auto flow control enable

    // LSR register signals
    logic iLSR_DR;                      // LSR: Data ready
    logic iLSR_OE;                      // LSR: Overrun error
    logic iLSR_PE;                      // LSR: Parity error
    logic iLSR_FE;                      // LSR: Framing error
    logic iLSR_BI;                      // LSR: Break Interrupt
    logic iLSR_THRE;                    // LSR: Transmitter holding register empty
    logic iLSR_TEMT;                    // LSR: Transmitter empty
    logic iLSR_FIFOERR;                 // LSR: Error in receiver FIFO

    // MSR register signals
    logic iMSR_dCTS;                    // MSR: Delta CTS
    logic iMSR_dDSR;                    // MSR: Delta DSR
    logic iMSR_TERI;                    // MSR: Trailing edge ring indicator
    logic iMSR_dDCD;                    // MSR: Delta DCD
    logic iMSR_CTS;                     // MSR: CTS
    logic iMSR_DSR;                     // MSR: DSR
    logic iMSR_RI;                      // MSR: RI
    logic iMSR_DCD;                     // MSR: DCD

    // UART MSR signals
    logic iCTSNs;                       // Synchronized CTSN input
    logic iDSRNs;                       // Synchronized DSRN input
    logic iDCDNs;                       // Synchronized DCDN input
    logic iRINs;                        // Synchronized RIN input
    logic iCTSn;                        // Filtered CTSN input
    logic iDSRn;                        // Filtered DSRN input
    logic iDCDn;                        // Filtered DCDN input
    logic iRIn;                         // Filtered RIN input
    logic iCTSnRE;                      // CTSn rising edge
    logic iCTSnFE;                      // CTSn falling edge
    logic iDSRnRE;                      // DSRn rising edge
    logic iDSRnFE;                      // DSRn falling edge
    logic iDCDnRE;                      // DCDn rising edge
    logic iDCDnFE;                      // DCDn falling edge
    logic iRInRE;                       // RIn rising edge
    logic iRInFE;                       // RIn falling edge

    // UART baudrate generation signals
    logic [15:0] iBaudgenDiv;           // Baudrate divider
    logic iBaudtick16x;                 // 16x Baudrate output from baudrate generator
    logic iBaudtick2x;                  // 2x Baudrate for transmitter
    logic iRCLK;                        // 16x Baudrate for receiver

    // UART FIFO signals
    logic iTXFIFOClear;                 // Clear TX FIFO
    logic iTXFIFOWrite;                 // Write to TX FIFO
    logic iTXFIFORead;                  // Read from TX FIFO
    logic iTXFIFOEmpty;                 // TX FIFO is empty
    logic iTXFIFOFull;                  // TX FIFO is full
    logic iTXFIFO16Full;                // TX FIFO 16 byte mode is full
    logic iTXFIFO64Full;                // TX FIFO 64 byte mode is full
    logic [5:0] iTXFIFOUsage;           // TX FIFO usage
    logic [7:0] iTXFIFOQ;               // TX FIFO output
    logic iRXFIFOClear;                 // Clear RX FIFO
    logic iRXFIFOWrite;                 // Write to RX FIFO
    logic iRXFIFORead;                  // Read from RX FIFO
    logic iRXFIFOEmpty;                 // RX FIFO is empty
    logic iRXFIFOFull;                  // RX FIFO is full
    logic iRXFIFO16Full;                // RX FIFO 16 byte mode is full
    logic iRXFIFO64Full;                // RX FIFO 64 byte mode is full
    logic [10:0] iRXFIFOD;              // RX FIFO input
    logic [10:0] iRXFIFOQ;              // RX FIFO output
    logic [5:0] iRXFIFOUsage;           // RX FIFO usage
    logic iRXFIFOTrigger;               // FIFO trigger level reached
    logic iRXFIFO16Trigger;             // FIFO 16 byte mode trigger level reached
    logic iRXFIFO64Trigger;             // FIFO 64 byte mode trigger level reached
    logic iRXFIFOPE;                    // Parity error from FIFO
    logic iRXFIFOFE;                    // Frame error from FIFO
    logic iRXFIFOBI;                    // Break interrupt from FIFO

    // UART transmitter signals
    logic iSOUT;                        // Transmitter output
    logic iTXStart;                     // Start transmitter
    logic iTXClear;                     // Clear transmitter status
    logic iTXFinished;                  // TX finished, character transmitted
    logic iTXRunning;                   // TX in progress

    // UART receiver signals
    logic iSINr;                        // Synchronized SIN input
    logic iSIN;                         // Receiver input
    logic iRXFinished;                  // RX finished, character received
    logic iRXClear;                     // Clear receiver status
    logic [7:0] iRXData;                // RX data
    logic iRXPE;                        // RX parity error
    logic iRXFE;                        // RX frame error
    logic iRXBI;                        // RX break interrupt

    // UART control signals
    logic iFERE;                        // Frame error detected
    logic iPERE;                        // Parity error detected
    logic iBIRE;                        // Break interrupt detected
    integer iFECounter;                 // FIFO error counter
    logic iFEIncrement;                 // FIFO error counter increment
    logic iFEDecrement;                 // FIFO error counter decrement
    logic iRDAInterrupt;                // Receiver data available interrupt
    logic [5:0] iTimeoutCount;          // Character timeout counter (FIFO mode)
    logic iCharTimeout;                 // Character timeout indication (FIFO mode)
    logic iLSR_THRERE;                  // LSR THRE rising edge for interrupt generation
    logic iTHRInterrupt;                // Transmitter holding register empty interrupt
    logic iTXEnable;                    // Transmitter enable signal
    logic iRTS;                         // Internal RTS signal with/without automatic flow control

    // Unused edge detect outputs
    logic unused_write_re, unused_read_re;
    logic unused_cts_re, unused_cts_fe;
    logic unused_dsr_re, unused_dsr_fe;
    logic unused_ri_re;
    logic unused_dcd_re, unused_dcd_fe;
    logic unused_pe_fe, unused_fe_fe, unused_bi_fe;
    logic unused_rclk_fe;
    logic unused_thre_fe;

    // ================================================================
    // Global device signals
    // ================================================================
    assign iCSWR = CS && WR;
    assign iCSRD = CS && RD;

    slib_edge_detect UART_ED_WRITE (
        .CLK(CLK), .RST(RST), .D(iCSWR), .RE(unused_write_re), .FE(iWriteFE)
    );
    slib_edge_detect UART_ED_READ (
        .CLK(CLK), .RST(RST), .D(iCSRD), .RE(unused_read_re), .FE(iReadFE)
    );

    assign iWrite = iWriteFE;
    assign iRead  = iReadFE;

    // UART registers read/write signals
    assign iRBRRead  = iRead  && (iA == 3'b000) && !iLCR_DLAB;
    assign iTHRWrite = iWrite && (iA == 3'b000) && !iLCR_DLAB;
    assign iDLLWrite = iWrite && (iA == 3'b000) && iLCR_DLAB;
    assign iDLMWrite = iWrite && (iA == 3'b001) && iLCR_DLAB;
    assign iIERWrite = iWrite && (iA == 3'b001) && !iLCR_DLAB;
    assign iIIRRead  = iRead  && (iA == 3'b010);
    assign iFCRWrite = iWrite && (iA == 3'b010);
    assign iLCRWrite = iWrite && (iA == 3'b011);
    assign iMCRWrite = iWrite && (iA == 3'b100);
    assign iLSRRead  = iRead  && (iA == 3'b101);
    assign iMSRRead  = iRead  && (iA == 3'b110);
    assign iSCRWrite = iWrite && (iA == 3'b111);

    // ================================================================
    // Async. input synchronization
    // ================================================================
    slib_input_sync UART_IS_SIN (.CLK(CLK), .RST(RST), .D(SIN),  .Q(iSINr));
    slib_input_sync UART_IS_CTS (.CLK(CLK), .RST(RST), .D(CTSN), .Q(iCTSNs));
    slib_input_sync UART_IS_DSR (.CLK(CLK), .RST(RST), .D(DSRN), .Q(iDSRNs));
    slib_input_sync UART_IS_DCD (.CLK(CLK), .RST(RST), .D(DCDN), .Q(iDCDNs));
    slib_input_sync UART_IS_RI  (.CLK(CLK), .RST(RST), .D(RIN),  .Q(iRINs));

    // Input filter for UART control signals
    slib_input_filter #(.SIZE(2)) UART_IF_CTS (.CLK(CLK), .RST(RST), .CE(iBaudtick2x), .D(iCTSNs), .Q(iCTSn));
    slib_input_filter #(.SIZE(2)) UART_IF_DSR (.CLK(CLK), .RST(RST), .CE(iBaudtick2x), .D(iDSRNs), .Q(iDSRn));
    slib_input_filter #(.SIZE(2)) UART_IF_DCD (.CLK(CLK), .RST(RST), .CE(iBaudtick2x), .D(iDCDNs), .Q(iDCDn));
    slib_input_filter #(.SIZE(2)) UART_IF_RI  (.CLK(CLK), .RST(RST), .CE(iBaudtick2x), .D(iRINs),  .Q(iRIn));

    // Sync. input synchronization
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iA   <= 3'b0;
            iDIN <= 8'b0;
        end else begin
            iA   <= A;
            iDIN <= DIN;
        end
    end

    // ================================================================
    // Divisor latch register
    // ================================================================
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iDLL <= 8'b0;
            iDLM <= 8'b0;
        end else begin
            if (iDLLWrite) iDLL <= iDIN;
            if (iDLMWrite) iDLM <= iDIN;
        end
    end

    // ================================================================
    // Interrupt enable register
    // ================================================================
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iIER <= 8'b0;
        end else begin
            if (iIERWrite) iIER <= {4'b0, iDIN[3:0]};
        end
    end

    // ================================================================
    // Interrupt control and IIR
    // ================================================================
    uart_interrupt UART_IIC (
        .CLK(CLK),
        .RST(RST),
        .IER(iIER[3:0]),
        .LSR(iLSR[4:0]),
        .THI(iTHRInterrupt),
        .RDA(iRDAInterrupt),
        .CTI(iCharTimeout),
        .AFE(iMCR_AFE),
        .MSR(iMSR[3:0]),
        .IIR(iIIR[3:0]),
        .INT(INT)
    );

    // THR empty interrupt
    slib_edge_detect UART_IIC_THRE_ED (
        .CLK(CLK), .RST(RST), .D(iLSR_THRE), .RE(iLSR_THRERE), .FE(unused_thre_fe)
    );

    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iTHRInterrupt <= 1'b0;
        end else begin
            if (iLSR_THRERE || iFCR_TXFIFOReset || (iIERWrite && iDIN[1] && iLSR_THRE))
                iTHRInterrupt <= 1'b1;     // Set on THRE, TX FIFO reset or ETBEI enable
            else if ((iIIRRead && iIIR[3:1] == 3'b001) || iTHRWrite)
                iTHRInterrupt <= 1'b0;     // Clear on IIR read (if source) or THR write
        end
    end

    assign iRDAInterrupt = (!iFCR_FIFOEnable && iLSR_DR) ||
                           (iFCR_FIFOEnable && iRXFIFOTrigger);

    assign iIIR[4]  = 1'b0;
    assign iIIR[5]  = iFCR_FIFOEnable ? iFCR_FIFO64E : 1'b0;
    assign iIIR[6]  = iFCR_FIFOEnable;
    assign iIIR[7]  = iFCR_FIFOEnable;

    // ================================================================
    // Character timeout indication
    // ================================================================
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iTimeoutCount <= 6'b0;
            iCharTimeout  <= 1'b0;
        end else begin
            if (iRXFIFOEmpty || iRBRRead || iRXFIFOWrite)
                iTimeoutCount <= 6'b0;
            else if (!iRXFIFOEmpty && iBaudtick2x && !iTimeoutCount[5])
                iTimeoutCount <= iTimeoutCount + 1'b1;

            // Timeout indication
            if (iFCR_FIFOEnable) begin
                if (iRBRRead)
                    iCharTimeout <= 1'b0;
                else if (iTimeoutCount[5])
                    iCharTimeout <= 1'b1;
            end else begin
                iCharTimeout <= 1'b0;
            end
        end
    end

    // ================================================================
    // FIFO control register
    // ================================================================
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iFCR_FIFOEnable  <= 1'b0;
            iFCR_RXFIFOReset <= 1'b0;
            iFCR_TXFIFOReset <= 1'b0;
            iFCR_DMAMode     <= 1'b0;
            iFCR_FIFO64E     <= 1'b0;
            iFCR_RXTrigger   <= 2'b0;
        end else begin
            // FIFO reset pulse only
            iFCR_RXFIFOReset <= 1'b0;
            iFCR_TXFIFOReset <= 1'b0;

            if (iFCRWrite) begin
                iFCR_FIFOEnable <= iDIN[0];
                iFCR_DMAMode    <= iDIN[3];
                iFCR_RXTrigger  <= iDIN[7:6];

                if (iLCR_DLAB)
                    iFCR_FIFO64E <= iDIN[5];

                // RX FIFO reset control
                if (iDIN[1] || (!iFCR_FIFOEnable && iDIN[0]) || (iFCR_FIFOEnable && !iDIN[0]))
                    iFCR_RXFIFOReset <= 1'b1;
                // TX FIFO reset control
                if (iDIN[2] || (!iFCR_FIFOEnable && iDIN[0]) || (iFCR_FIFOEnable && !iDIN[0]))
                    iFCR_TXFIFOReset <= 1'b1;
            end
        end
    end

    // ================================================================
    // Line control register
    // ================================================================
    always_ff @(posedge CLK or posedge RST) begin
        if (RST)
            iLCR <= 8'b0;
        else if (iLCRWrite)
            iLCR <= iDIN;
    end

    assign iLCR_WLS  = iLCR[1:0];
    assign iLCR_STB  = iLCR[2];
    assign iLCR_PEN  = iLCR[3];
    assign iLCR_EPS  = iLCR[4];
    assign iLCR_SP   = iLCR[5];
    assign iLCR_BC   = iLCR[6];
    assign iLCR_DLAB = iLCR[7];

    // ================================================================
    // Modem control register
    // ================================================================
    always_ff @(posedge CLK or posedge RST) begin
        if (RST)
            iMCR <= 8'b0;
        else if (iMCRWrite)
            iMCR <= {2'b0, iDIN[5:0]};
    end

    assign iMCR_DTR  = iMCR[0];
    assign iMCR_RTS  = iMCR[1];
    assign iMCR_OUT1 = iMCR[2];
    assign iMCR_OUT2 = iMCR[3];
    assign iMCR_LOOP = iMCR[4];
    assign iMCR_AFE  = iMCR[5];

    // ================================================================
    // Line status register
    // ================================================================
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iLSR_OE    <= 1'b0;
            iLSR_PE    <= 1'b0;
            iLSR_FE    <= 1'b0;
            iLSR_BI    <= 1'b0;
            iFECounter <= 0;
        end else begin
            // Overrun error
            if ((!iFCR_FIFOEnable && iLSR_DR && iRXFinished) ||
                (iFCR_FIFOEnable && iRXFIFOFull && iRXFinished))
                iLSR_OE <= 1'b1;
            else if (iLSRRead)
                iLSR_OE <= 1'b0;

            // Parity error
            if (iPERE)
                iLSR_PE <= 1'b1;
            else if (iLSRRead)
                iLSR_PE <= 1'b0;

            // Frame error
            if (iFERE)
                iLSR_FE <= 1'b1;
            else if (iLSRRead)
                iLSR_FE <= 1'b0;

            // Break interrupt
            if (iBIRE)
                iLSR_BI <= 1'b1;
            else if (iLSRRead)
                iLSR_BI <= 1'b0;

            // FIFO error counter
            if (iRXFIFOClear)
                iFECounter <= 0;
            else begin
                if (iFEIncrement && !iFEDecrement)
                    iFECounter <= iFECounter + 1;
                else if (!iFEIncrement && iFEDecrement)
                    iFECounter <= iFECounter - 1;
            end
        end
    end

    // FIFO error
    always_ff @(posedge CLK or posedge RST) begin
        if (RST)
            iLSR_FIFOERR <= 1'b0;
        else begin
            if (iFECounter != 0)
                iLSR_FIFOERR <= 1'b1;
            else if (iRXFIFOEmpty || iRXFIFOQ[10:8] == 3'b000)
                iLSR_FIFOERR <= 1'b0;
        end
    end

    assign iRXFIFOPE = !iRXFIFOEmpty && iRXFIFOQ[8];
    assign iRXFIFOFE = !iRXFIFOEmpty && iRXFIFOQ[9];
    assign iRXFIFOBI = !iRXFIFOEmpty && iRXFIFOQ[10];

    slib_edge_detect UART_PEDET (.CLK(CLK), .RST(RST), .D(iRXFIFOPE), .RE(iPERE), .FE(unused_pe_fe));
    slib_edge_detect UART_FEDET (.CLK(CLK), .RST(RST), .D(iRXFIFOFE), .RE(iFERE), .FE(unused_fe_fe));
    slib_edge_detect UART_BIDET (.CLK(CLK), .RST(RST), .D(iRXFIFOBI), .RE(iBIRE), .FE(unused_bi_fe));

    assign iFEIncrement = iRXFIFOWrite && (iRXFIFOD[10:8] != 3'b000);
    assign iFEDecrement = (iFECounter != 0) && !iRXFIFOEmpty && (iPERE || iFERE || iBIRE);

    assign iLSR[0] = iLSR_DR;
    assign iLSR[1] = iLSR_OE;
    assign iLSR[2] = iLSR_PE;
    assign iLSR[3] = iLSR_FE;
    assign iLSR[4] = iLSR_BI;
    assign iLSR[5] = iLSR_THRE;
    assign iLSR[6] = iLSR_TEMT;
    assign iLSR[7] = iFCR_FIFOEnable && iLSR_FIFOERR;

    assign iLSR_DR   = !iRXFIFOEmpty || iRXFIFOWrite;
    assign iLSR_THRE = iTXFIFOEmpty;
    assign iLSR_TEMT = !iTXRunning && iLSR_THRE;

    // ================================================================
    // Modem status register
    // ================================================================
    assign iMSR_CTS = (iMCR_LOOP && iRTS)       || (!iMCR_LOOP && !iCTSn);
    assign iMSR_DSR = (iMCR_LOOP && iMCR_DTR)   || (!iMCR_LOOP && !iDSRn);
    assign iMSR_RI  = (iMCR_LOOP && iMCR_OUT1)  || (!iMCR_LOOP && !iRIn);
    assign iMSR_DCD = (iMCR_LOOP && iMCR_OUT2)  || (!iMCR_LOOP && !iDCDn);

    // Edge detection for CTS, DSR, DCD and RI
    slib_edge_detect UART_ED_CTS (.CLK(CLK), .RST(RST), .D(iMSR_CTS), .RE(iCTSnRE), .FE(iCTSnFE));
    slib_edge_detect UART_ED_DSR (.CLK(CLK), .RST(RST), .D(iMSR_DSR), .RE(iDSRnRE), .FE(iDSRnFE));
    slib_edge_detect UART_ED_RI  (.CLK(CLK), .RST(RST), .D(iMSR_RI),  .RE(iRInRE),  .FE(iRInFE));
    slib_edge_detect UART_ED_DCD (.CLK(CLK), .RST(RST), .D(iMSR_DCD), .RE(iDCDnRE), .FE(iDCDnFE));

    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iMSR_dCTS <= 1'b0;
            iMSR_dDSR <= 1'b0;
            iMSR_TERI <= 1'b0;
            iMSR_dDCD <= 1'b0;
        end else begin
            // Delta CTS
            if (iCTSnRE || iCTSnFE)
                iMSR_dCTS <= 1'b1;
            else if (iMSRRead)
                iMSR_dCTS <= 1'b0;

            // Delta DSR
            if (iDSRnRE || iDSRnFE)
                iMSR_dDSR <= 1'b1;
            else if (iMSRRead)
                iMSR_dDSR <= 1'b0;

            // Trailing edge RI
            if (iRInFE)
                iMSR_TERI <= 1'b1;
            else if (iMSRRead)
                iMSR_TERI <= 1'b0;

            // Delta DCD
            if (iDCDnRE || iDCDnFE)
                iMSR_dDCD <= 1'b1;
            else if (iMSRRead)
                iMSR_dDCD <= 1'b0;
        end
    end

    assign iMSR[0] = iMSR_dCTS;
    assign iMSR[1] = iMSR_dDSR;
    assign iMSR[2] = iMSR_TERI;
    assign iMSR[3] = iMSR_dDCD;
    assign iMSR[4] = iMSR_CTS;
    assign iMSR[5] = iMSR_DSR;
    assign iMSR[6] = iMSR_RI;
    assign iMSR[7] = iMSR_DCD;

    // ================================================================
    // Scratch register
    // ================================================================
    always_ff @(posedge CLK or posedge RST) begin
        if (RST)
            iSCR <= 8'b0;
        else if (iSCRWrite)
            iSCR <= iDIN;
    end

    // ================================================================
    // Baudrate generator
    // ================================================================
    assign iBaudgenDiv = {iDLM, iDLL};

    uart_baudgen UART_BG16 (
        .CLK(CLK),
        .RST(RST),
        .CE(BAUDCE),
        .CLEAR(1'b0),
        .DIVIDER(iBaudgenDiv),
        .BAUDTICK(iBaudtick16x)
    );

    slib_clock_div #(.RATIO(8)) UART_BG2 (
        .CLK(CLK),
        .RST(RST),
        .CE(iBaudtick16x),
        .Q(iBaudtick2x)
    );

    slib_edge_detect UART_RCLK (
        .CLK(CLK),
        .RST(RST),
        .D(RCLK),
        .RE(iRCLK),
        .FE(unused_rclk_fe)
    );

    // ================================================================
    // Transmitter FIFO
    // ================================================================
    slib_fifo #(.WIDTH(8), .SIZE_E(6)) UART_TXFF (
        .CLK(CLK),
        .RST(RST),
        .CLEAR(iTXFIFOClear),
        .WRITE(iTXFIFOWrite),
        .READ(iTXFIFORead),
        .D(iDIN),
        .Q(iTXFIFOQ),
        .EMPTY(iTXFIFOEmpty),
        .FULL(iTXFIFO64Full),
        .USAGE(iTXFIFOUsage)
    );

    assign iTXFIFO16Full = iTXFIFOUsage[4];
    assign iTXFIFOFull   = iFCR_FIFO64E ? iTXFIFO64Full : iTXFIFO16Full;
    assign iTXFIFOWrite  = ((!iFCR_FIFOEnable && iTXFIFOEmpty) ||
                            (iFCR_FIFOEnable && !iTXFIFOFull)) && iTHRWrite;
    assign iTXFIFOClear  = iFCR_TXFIFOReset;

    // ================================================================
    // Receiver FIFO
    // ================================================================
    slib_fifo #(.WIDTH(11), .SIZE_E(6)) UART_RXFF (
        .CLK(CLK),
        .RST(RST),
        .CLEAR(iRXFIFOClear),
        .WRITE(iRXFIFOWrite),
        .READ(iRXFIFORead),
        .D(iRXFIFOD),
        .Q(iRXFIFOQ),
        .EMPTY(iRXFIFOEmpty),
        .FULL(iRXFIFO64Full),
        .USAGE(iRXFIFOUsage)
    );

    assign iRXFIFORead    = iRBRRead;
    assign iRXFIFO16Full  = iRXFIFOUsage[4];
    assign iRXFIFOFull    = iFCR_FIFO64E ? iRXFIFO64Full : iRXFIFO16Full;
    assign iRBR           = iRXFIFOQ[7:0];

    // FIFO trigger level: 1, 4, 8, 14
    assign iRXFIFO16Trigger = (iFCR_RXTrigger == 2'b00 && !iRXFIFOEmpty) ||
                              (iFCR_RXTrigger == 2'b01 && (iRXFIFOUsage[2] || iRXFIFOUsage[3])) ||
                              (iFCR_RXTrigger == 2'b10 && iRXFIFOUsage[3]) ||
                              (iFCR_RXTrigger == 2'b11 && iRXFIFOUsage[3] && iRXFIFOUsage[2] && iRXFIFOUsage[1]) ||
                              iRXFIFO16Full;

    // FIFO 64 trigger level: 1, 16, 32, 56
    assign iRXFIFO64Trigger = (iFCR_RXTrigger == 2'b00 && !iRXFIFOEmpty) ||
                              (iFCR_RXTrigger == 2'b01 && (iRXFIFOUsage[4] || iRXFIFOUsage[5])) ||
                              (iFCR_RXTrigger == 2'b10 && iRXFIFOUsage[5]) ||
                              (iFCR_RXTrigger == 2'b11 && iRXFIFOUsage[5] && iRXFIFOUsage[4] && iRXFIFOUsage[3]) ||
                              iRXFIFO64Full;

    assign iRXFIFOTrigger = iFCR_FIFO64E ? iRXFIFO64Trigger : iRXFIFO16Trigger;

    // ================================================================
    // Transmitter
    // ================================================================
    uart_transmitter UART_TX (
        .CLK(CLK),
        .RST(RST),
        .TXCLK(iBaudtick2x),
        .TXSTART(iTXStart),
        .CLEAR(iTXClear),
        .WLS(iLCR_WLS),
        .STB(iLCR_STB),
        .PEN(iLCR_PEN),
        .EPS(iLCR_EPS),
        .SP(iLCR_SP),
        .BC(iLCR_BC),
        .DIN(iTSR),
        .TXFINISHED(iTXFinished),
        .SOUT(iSOUT)
    );

    assign iTXClear = 1'b0;

    // ================================================================
    // Receiver
    // ================================================================
    uart_receiver UART_RX (
        .CLK(CLK),
        .RST(RST),
        .RXCLK(iRCLK),
        .RXCLEAR(iRXClear),
        .WLS(iLCR_WLS),
        .STB(iLCR_STB),
        .PEN(iLCR_PEN),
        .EPS(iLCR_EPS),
        .SP(iLCR_SP),
        .SIN(iSIN),
        .PE(iRXPE),
        .FE(iRXFE),
        .BI(iRXBI),
        .DOUT(iRXData),
        .RXFINISHED(iRXFinished)
    );

    assign iRXClear = 1'b0;
    assign iSIN = iMCR_LOOP ? iSOUT : iSINr;

    // ================================================================
    // Transmitter enable signal
    // ================================================================
    assign iTXEnable = !iTXFIFOEmpty && (!iMCR_AFE || (iMCR_AFE && iMSR_CTS));

    // ================================================================
    // Transmitter process
    // ================================================================
    typedef enum logic [1:0] {
        TX_IDLE    = 2'd0,
        TX_START   = 2'd1,
        TX_RUN     = 2'd2,
        TX_END     = 2'd3
    } tx_state_t;

    tx_state_t tx_state;

    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            tx_state    <= TX_IDLE;
            iTSR        <= 8'b0;
            iTXStart    <= 1'b0;
            iTXFIFORead <= 1'b0;
            iTXRunning  <= 1'b0;
        end else begin
            // Defaults
            iTXStart    <= 1'b0;
            iTXFIFORead <= 1'b0;
            iTXRunning  <= 1'b0;

            case (tx_state)
                TX_IDLE: begin
                    if (iTXEnable) begin
                        iTXStart <= 1'b1;       // Start transmitter
                        tx_state <= TX_START;
                    end
                end

                TX_START: begin
                    iTSR        <= iTXFIFOQ;
                    iTXStart    <= 1'b1;        // Start transmitter
                    iTXFIFORead <= 1'b1;        // Increment TX FIFO read counter
                    tx_state    <= TX_RUN;
                end

                TX_RUN: begin
                    if (iTXFinished)            // TX finished
                        tx_state <= TX_END;
                    iTXRunning <= 1'b1;
                    iTXStart   <= 1'b1;
                end

                TX_END: begin
                    tx_state <= TX_IDLE;
                end
            endcase
        end
    end

    // ================================================================
    // Receiver process
    // ================================================================
    typedef enum logic {
        RX_IDLE = 1'b0,
        RX_SAVE = 1'b1
    } rx_state_t;

    rx_state_t rx_state;

    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            rx_state     <= RX_IDLE;
            iRXFIFOWrite <= 1'b0;
            iRXFIFOClear <= 1'b0;
            iRXFIFOD     <= 11'b0;
        end else begin
            // Defaults
            iRXFIFOWrite <= 1'b0;
            iRXFIFOClear <= iFCR_RXFIFOReset;

            case (rx_state)
                RX_IDLE: begin
                    if (iRXFinished) begin      // Receive finished
                        iRXFIFOD <= {iRXBI, iRXFE, iRXPE, iRXData};
                        if (!iFCR_FIFOEnable)
                            iRXFIFOClear <= 1'b1;   // Non-FIFO mode
                        rx_state <= RX_SAVE;
                    end
                end

                RX_SAVE: begin
                    if (!iFCR_FIFOEnable)
                        iRXFIFOWrite <= 1'b1;       // Non-FIFO mode: Overwrite
                    else if (!iRXFIFOFull)
                        iRXFIFOWrite <= 1'b1;       // FIFO mode
                    rx_state <= RX_IDLE;
                end
            endcase
        end
    end

    // ================================================================
    // Automatic flow control
    // ================================================================
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iRTS <= 1'b0;
        end else begin
            if (!iMCR_RTS || (iMCR_AFE && iRXFIFOTrigger))
                // Deassert when MCR_RTS not set or AFC enabled and RX FIFO trigger reached
                iRTS <= 1'b0;
            else if (iMCR_RTS && (!iMCR_AFE || (iMCR_AFE && iRXFIFOEmpty)))
                // Assert when MCR_RTS set and AFC disabled or when AFC enabled and RX FIFO empty
                iRTS <= 1'b1;
        end
    end

    // ================================================================
    // Output registers
    // ================================================================
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            DDIS     <= 1'b0;
            BAUDOUTN <= 1'b0;
            OUT1N    <= 1'b0;
            OUT2N    <= 1'b0;
            RTSN     <= 1'b0;
            DTRN     <= 1'b0;
            SOUT     <= 1'b0;
        end else begin
            // Default values
            DDIS     <= 1'b0;
            BAUDOUTN <= 1'b0;
            OUT1N    <= 1'b0;
            OUT2N    <= 1'b0;
            RTSN     <= 1'b0;
            DTRN     <= 1'b0;
            SOUT     <= 1'b0;

            // DDIS
            if (!CS || !RD)
                DDIS <= 1'b1;

            // BAUDOUTN
            if (!iBaudtick16x)
                BAUDOUTN <= 1'b1;

            // OUT1N
            if (iMCR_LOOP || !iMCR_OUT1)
                OUT1N <= 1'b1;

            // OUT2N
            if (iMCR_LOOP || !iMCR_OUT2)
                OUT2N <= 1'b1;

            // RTS
            if (iMCR_LOOP || !iRTS)
                RTSN <= 1'b1;

            // DTR
            if (iMCR_LOOP || !iMCR_DTR)
                DTRN <= 1'b1;

            // SOUT
            if (iMCR_LOOP || iSOUT)
                SOUT <= 1'b1;
        end
    end

    // ================================================================
    // UART data output
    // ================================================================
    always_comb begin
        case (iA)
            3'b000:  DOUT = iLCR_DLAB ? iDLL : iRBR;
            3'b001:  DOUT = iLCR_DLAB ? iDLM : iIER;
            3'b010:  DOUT = iIIR;
            3'b011:  DOUT = iLCR;
            3'b100:  DOUT = iMCR;
            3'b101:  DOUT = iLSR;
            3'b110:  DOUT = iMSR;
            3'b111:  DOUT = iSCR;
            default: DOUT = iRBR;
        endcase
    end

endmodule
