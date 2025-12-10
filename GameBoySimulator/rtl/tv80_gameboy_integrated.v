//
// TV80-based GameBoy CPU with integrated timing control
// This version integrates the wrapper logic into a single module
// for precise control over DO/WR_n timing relationships
//
// Copyright (c) 2024 - MIT License
//

module GBse #(
    parameter T2Write = 2,  // 0 => WR_n active in T3, 1 => WR_n active in T2, Other => WR_n active in T2+T3
    parameter IOWait = 1    // 0 => Single cycle I/O, 1 => Std I/O cycle
) (
    input         RESET_n,
    input         CLK_n,
    input         CLKEN,
    input         WAIT_n,
    input         INT_n,
    input         NMI_n,
    input         BUSRQ_n,
    output        M1_n,
    output reg    MREQ_n,
    output reg    IORQ_n,
    output reg    RD_n,
    output reg    WR_n,
    output        RFSH_n,
    output        HALT_n,
    output        BUSAK_n,
    output        STOP,
    output [15:0] A,
    input  [7:0]  DI,
    output [7:0]  DO,
    input         isGBC,
    // Savestate interface (stubbed for now)
    input  [63:0] SaveStateBus_Din,
    input  [9:0]  SaveStateBus_Adr,
    input         SaveStateBus_wren,
    input         SaveStateBus_rst,
    output [63:0] SaveStateBus_Dout
);

    // Internal signals from tv80_core
    wire        intcycle_n;
    wire        no_read;
    wire        write;
    wire        iorq;
    wire [7:0]  dout_core;
    reg  [7:0]  di_reg;
    wire [6:0]  mcycle;
    wire [6:0]  tstate;

    // Timing control for DO output
    // We'll register DO one extra time to ensure it's stable before WR_n
    reg  [7:0]  do_buffered;

    // Stub savestate output
    assign SaveStateBus_Dout = 64'b0;

    // Instantiate TV80 core with GameBoy mode
    tv80_core #(
        .Mode(3),           // GameBoy mode (LR35902)
        .IOWait(IOWait)
    ) i_tv80_core (
        .cen        (CLKEN),
        .m1_n       (M1_n),
        .iorq       (iorq),
        .no_read    (no_read),
        .write      (write),
        .rfsh_n     (RFSH_n),
        .halt_n     (HALT_n),
        .wait_n     (WAIT_n),
        .int_n      (INT_n),
        .nmi_n      (NMI_n),
        .reset_n    (RESET_n),
        .busrq_n    (BUSRQ_n),
        .busak_n    (BUSAK_n),
        .clk        (CLK_n),
        .IntE       (),
        .stop       (STOP),
        .A          (A),
        .dinst      (DI),
        .di         (di_reg),
        .dout       (dout_core),
        .mc         (mcycle),
        .ts         (tstate),
        .intcycle_n (intcycle_n)
    );

    // KEY FIX: Buffer DO to ensure it's stable one clock before WR_n
    // This breaks the race condition between BusB->dout and WR_n assertion
    always @(posedge CLK_n or negedge RESET_n) begin
        if (!RESET_n) begin
            do_buffered <= 8'h00;
        end
        else begin
            // Update buffered DO every clock cycle (not gated by CLKEN)
            // This ensures external DO is always one clock behind core dout
            do_buffered <= dout_core;
        end
    end

    // External DO output uses buffered value
    assign DO = do_buffered;

    // Control signal generation with proper timing
    always @(posedge CLK_n or negedge RESET_n) begin
        if (!RESET_n) begin
            RD_n   <= 1'b1;
            WR_n   <= 1'b1;
            IORQ_n <= 1'b1;
            MREQ_n <= 1'b1;
            di_reg <= 8'h00;
        end
        else begin
            // Control signals update every clock (not gated by CLKEN)
            // The CPU core gates internal state with CLKEN, but bus signals need continuous updates
            RD_n   <= 1'b1;
            WR_n   <= 1'b1;
            IORQ_n <= 1'b1;
            MREQ_n <= 1'b1;

            if (mcycle[0]) begin
                // M1 cycle (instruction fetch)
                if (tstate[1] || tstate[2]) begin
                    RD_n   <= ~intcycle_n;
                    MREQ_n <= ~intcycle_n;
                end
                if (tstate[3]) begin
                    MREQ_n <= 1'b0;
                end
            end
            else if (mcycle[2] && intcycle_n == 1'b0) begin
                // Interrupt acknowledge cycle
                if (tstate[2]) begin
                    IORQ_n <= 1'b0;
                end
            end
            else begin
                // Memory/IO read
                if ((tstate[1] || tstate[2]) && no_read == 1'b0 && write == 1'b0) begin
                    RD_n   <= 1'b0;
                    IORQ_n <= ~iorq;
                    MREQ_n <= iorq;
                end

                // Memory/IO write - T2Write timing variants
                // CRITICAL: Now that DO is buffered, WR_n sees stable data
                if (T2Write == 0) begin
                    if (tstate[2] && write == 1'b1) begin
                        WR_n   <= 1'b0;
                        IORQ_n <= ~iorq;
                        MREQ_n <= iorq;
                    end
                end
                else if (T2Write == 1) begin
                    if ((tstate[1] || (tstate[2] && WAIT_n == 1'b0)) && write == 1'b1) begin
                        WR_n   <= 1'b0;
                        IORQ_n <= ~iorq;
                        MREQ_n <= iorq;
                    end
                end
                else begin
                    // T2Write == 2 or other (default for GameBoy)
                    if ((tstate[1] || tstate[2]) && write == 1'b1) begin
                        WR_n   <= 1'b0;
                        IORQ_n <= ~iorq;
                        MREQ_n <= iorq;
                    end
                end
            end

            // Data input register latch
            // Latch at T2 during READ cycles only
            if (CLKEN && tstate[2] && WAIT_n == 1'b1 && !write && !no_read) begin
                di_reg <= DI;
            end
        end
    end

endmodule
