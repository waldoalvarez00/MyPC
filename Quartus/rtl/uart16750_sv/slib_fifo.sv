//
// FIFO
//
// Author:   Sebastian Witt (original VHDL)
// Translator: Claude AI (VHDL to SystemVerilog)
// Date:     29.01.2008 (original)
// Version:  1.3
//
// This code is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.

`default_nettype none

module slib_fifo #(
    parameter WIDTH   = 8,      // FIFO width
    parameter SIZE_E  = 6       // FIFO size (2^SIZE_E)
)(
    input  logic                CLK,        // Clock
    input  logic                RST,        // Reset
    input  logic                CLEAR,      // Clear FIFO
    input  logic                WRITE,      // Write to FIFO
    input  logic                READ,       // Read from FIFO
    input  logic [WIDTH-1:0]    D,          // FIFO input
    output logic [WIDTH-1:0]    Q,          // FIFO output
    output logic                EMPTY,      // FIFO is empty
    output logic                FULL,       // FIFO is full
    output logic [SIZE_E-1:0]   USAGE       // FIFO usage
);

    // Internal signals
    logic                   iEMPTY;
    logic                   iFULL;
    logic [SIZE_E:0]        iWRAddr;        // Write address (extra bit for full detection)
    logic [SIZE_E:0]        iRDAddr;        // Read address (extra bit for full detection)
    logic [SIZE_E-1:0]      iUSAGE;

    // FIFO memory
    logic [WIDTH-1:0] iFIFOMem [0:2**SIZE_E-1];

    // Full signal (read and write addresses match except MSB)
    assign iFULL = (iRDAddr[SIZE_E-1:0] == iWRAddr[SIZE_E-1:0]) &&
                   (iRDAddr[SIZE_E] != iWRAddr[SIZE_E]);

    // Write/read address counter and empty signal
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iWRAddr <= '0;
            iRDAddr <= '0;
            iEMPTY  <= 1'b1;
        end else begin
            if (WRITE && !iFULL) begin          // Write to FIFO
                iWRAddr <= iWRAddr + 1'b1;
            end

            if (READ && !iEMPTY) begin          // Read from FIFO
                iRDAddr <= iRDAddr + 1'b1;
            end

            if (CLEAR) begin                     // Reset FIFO
                iWRAddr <= '0;
                iRDAddr <= '0;
            end

            // Empty signal (read address same as write address)
            if (iRDAddr == iWRAddr) begin
                iEMPTY <= 1'b1;
            end else begin
                iEMPTY <= 1'b0;
            end
        end
    end

    // FIFO memory process
    always_ff @(posedge CLK) begin
        if (WRITE && !iFULL) begin
            iFIFOMem[iWRAddr[SIZE_E-1:0]] <= D;
        end
        Q <= iFIFOMem[iRDAddr[SIZE_E-1:0]];
    end

    // Usage counter
    always_ff @(posedge CLK or posedge RST) begin
        if (RST) begin
            iUSAGE <= '0;
        end else begin
            if (CLEAR) begin
                iUSAGE <= '0;
            end else begin
                if (!READ && WRITE && !iFULL) begin
                    iUSAGE <= iUSAGE + 1'b1;
                end
                if (!WRITE && READ && !iEMPTY) begin
                    iUSAGE <= iUSAGE - 1'b1;
                end
            end
        end
    end

    // Output signals
    assign EMPTY = iEMPTY;
    assign FULL  = iFULL;
    assign USAGE = iUSAGE;

endmodule

`default_nettype wire
