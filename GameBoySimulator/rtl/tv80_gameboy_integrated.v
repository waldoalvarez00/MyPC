//
// TV80-based GameBoy CPU with integrated timing control
// This version integrates the wrapper logic into a single module
// for precise control over DO/WR_n timing relationships
//
// Copyright (c) 2024 - MIT License
//

module GBse #(
    // Default to T3-only writes to ensure data is stable before the write pulse
    // is detected in `gb.v` (it edge-detects `WR_n` and uses `cpu_do` on the next
    // `clk_sys` rising edge). With TV80's internal state updates on posedge,
    // driving WR_n low in T2 can produce a falling edge before `dout` reflects
    // the selected BusB source for the write cycle (notably breaks PUSH/POP AF
    // in the DMG boot ROM).
    parameter T2Write = 0,  // 0 => WR_n active in T3, 1 => WR_n active in T2, Other => WR_n active in T2+T3
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
    wire [7:0]  dout_next;    // Combinational data output for proper write timing
    reg  [7:0]  di_reg;
    reg         wait_n_prev;
    wire [6:0]  mcycle;
    wire [6:0]  tstate;

    // Stub savestate output
    assign SaveStateBus_Dout = 64'b0;

    // Use combinational dout_next for DO - ensures valid data during write cycles
    assign DO = dout_next;

    // Instantiate TV80 core with GameBoy mode
    tv80_core #(
        .Mode(3),           // GameBoy mode (LR35902)
        .IOWait(IOWait),
        // Game Boy flag bit positions (Z N H C in bits 7..4).
        // Matches MiSTer T80 GBse.vhd configuration.
        .Flag_S(0),
        .Flag_P(0),
        .Flag_X(0),
        .Flag_Y(0),
        .Flag_C(4),
        .Flag_H(5),
        .Flag_N(6),
        .Flag_Z(7)
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
        // Match the original GBse wrapper behavior: feed the instruction stream
        // directly from the system data bus. Sampling on the opposite clock edge
        // caused occasional opcode byte skew under synchronous memories (boot ROM),
        // which breaks CB-prefix sequences (e.g., CB 11 decoded as LD DE,d16).
        .dinst      (DI),
        .di         (di_reg),
        .dout       (),                 // Not used - using dout_next for proper write timing
        .dout_next  (dout_next),        // Combinational output for writes
        .mc         (mcycle),
        .ts         (tstate),
        .intcycle_n (intcycle_n)
    );

    // Control signal generation
    //
    // tv80_core updates `mcycle`/`tstate` and `dout` on the rising edge when CLKEN
    // is asserted. If we also update bus strobes on that same edge, the strobe
    // logic sees the *previous* `mcycle`/`tstate` (nonblocking update ordering)
    // and can lag by one T-state, which breaks opcode fetch under realistic SDRAM
    // latency (stale dinst sampled).
    //
    // Update bus strobes on the falling edge instead, after the core state has
    // settled, while still keeping them registered (stable) within each T-state.
    always @(negedge CLK_n or negedge RESET_n) begin
        if (!RESET_n) begin
            RD_n   <= 1'b1;
            WR_n   <= 1'b1;
            IORQ_n <= 1'b1;
            MREQ_n <= 1'b1;
        end else begin
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
            end else if (mcycle[2] && intcycle_n == 1'b0) begin
                // Interrupt acknowledge cycle
                if (tstate[2]) begin
                    IORQ_n <= 1'b0;
                end
            end else begin
                // Memory/IO read
                if ((tstate[1] || tstate[2]) && no_read == 1'b0 && write == 1'b0) begin
                    RD_n   <= 1'b0;
                    IORQ_n <= ~iorq;
                    MREQ_n <= iorq;
                end

                // Memory/IO write - T2Write timing variants
                if (T2Write == 0) begin
                    if (tstate[2] && write == 1'b1) begin
                        WR_n   <= 1'b0;
                        IORQ_n <= ~iorq;
                        MREQ_n <= iorq;
                    end
                end else if (T2Write == 1) begin
                    if ((tstate[1] || (tstate[2] && WAIT_n == 1'b0)) && write == 1'b1) begin
                        WR_n   <= 1'b0;
                        IORQ_n <= ~iorq;
                        MREQ_n <= iorq;
                    end
                end else begin
                    // T2Write == 2 or other (default for GameBoy)
                    if ((tstate[1] || tstate[2]) && write == 1'b1) begin
                        WR_n   <= 1'b0;
                        IORQ_n <= ~iorq;
                        MREQ_n <= iorq;
                    end
                end
            end
        end
    end

    // Data input register latch (matches the original VHDL GBse behavior).
    //
    // Latch on T3 during read cycles when the CPU advances (CLKEN), and also
    // once on WAIT_n rising edge to pre-latch data before CLKEN resumes after
    // SDRAM wait stretching.
    always @(posedge CLK_n or negedge RESET_n) begin
        if (!RESET_n) begin
            di_reg <= 8'h00;
            wait_n_prev <= 1'b1;
        end else begin
            if ((CLKEN || (!wait_n_prev && WAIT_n)) &&
                tstate[2] && WAIT_n == 1'b1 && !write && !no_read) begin
                di_reg <= DI;
            end
            wait_n_prev <= WAIT_n;
        end
    end

endmodule
