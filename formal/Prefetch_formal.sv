// Formal harness for Quartus/rtl/CPU/Prefetch.sv

`default_nettype none

module Prefetch_formal(
    input clk
);
    // Clock and reset
    reg reset;

    // Address control
    (* anyseq *) reg [15:0] new_cs;
    (* anyseq *) reg [15:0] new_ip;
    (* anyseq *) reg        load_new_ip;

    // FIFO interface
    wire        fifo_wr_en;
    wire [7:0]  fifo_wr_data;
    wire        fifo_reset;
    (* anyseq *) reg        fifo_full;

    // Memory port
    wire        mem_access;
    (* anyseq *) reg        mem_ack;
    wire [19:1] mem_address;
    (* anyseq *) reg [15:0] mem_data;

    // DUT
    Prefetch dut (
        .clk(clk),
        .reset(reset),

        .new_cs(new_cs),
        .new_ip(new_ip),
        .load_new_ip(load_new_ip),

        .fifo_wr_en(fifo_wr_en),
        .fifo_wr_data(fifo_wr_data),
        .fifo_reset(fifo_reset),
        .fifo_full(fifo_full),

        .mem_access(mem_access),
        .mem_ack(mem_ack),
        .mem_address(mem_address),
        .mem_data(mem_data)
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

    // Environment assumptions
    always @(posedge clk) if (seen_reset && !reset) begin
        // Memory only acknowledges when an access is active.
        if (!$past(reset) && mem_ack)
            assume($past(mem_access));
    end

    // Safety properties
    always @(posedge clk) if (seen_reset && !reset) begin
        // FIFO reset and write should not happen in the same cycle.
        assert(!(fifo_reset && fifo_wr_en));
    end

endmodule
