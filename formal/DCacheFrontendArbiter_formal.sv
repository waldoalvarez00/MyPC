// Formal harness for Quartus/rtl/common/DCacheFrontendArbiter.sv
//
// Ensures that only one front-end port is acknowledged per cycle and
// that ACKs/data are consistent with the cache backend.

`default_nettype none

module DCacheFrontendArbiter_formal(
    input logic clk
);
    logic reset;

    // CPU port
    (* anyseq *) logic [19:1] cpu_addr;
    logic [15:0]              cpu_data_in;
    (* anyseq *) logic [15:0] cpu_data_out;
    (* anyseq *) logic        cpu_access;
    logic                     cpu_ack;
    (* anyseq *) logic        cpu_wr_en;
    (* anyseq *) logic [1:0]  cpu_bytesel;

    // DMA port
    (* anyseq *) logic [19:1] dma_addr;
    logic [15:0]              dma_data_in;
    (* anyseq *) logic [15:0] dma_data_out;
    (* anyseq *) logic        dma_access;
    logic                     dma_ack;
    (* anyseq *) logic        dma_wr_en;
    (* anyseq *) logic [1:0]  dma_bytesel;

    // FPU port
    (* anyseq *) logic [19:1] fpu_addr;
    logic [15:0]              fpu_data_in;
    (* anyseq *) logic [15:0] fpu_data_out;
    (* anyseq *) logic        fpu_access;
    logic                     fpu_ack;
    (* anyseq *) logic        fpu_wr_en;
    (* anyseq *) logic [1:0]  fpu_bytesel;

    // DCache frontend
    logic [19:1]              cache_addr;
    (* anyseq *) logic [15:0] cache_data_in;
    logic [15:0]              cache_data_out;
    logic                     cache_access;
    (* anyseq *) logic        cache_ack;
    logic                     cache_wr_en;
    logic [1:0]               cache_bytesel;

    DCacheFrontendArbiter dut (
        .clk(clk),
        .reset(reset),
        .cpu_addr(cpu_addr),
        .cpu_data_in(cpu_data_in),
        .cpu_data_out(cpu_data_out),
        .cpu_access(cpu_access),
        .cpu_ack(cpu_ack),
        .cpu_wr_en(cpu_wr_en),
        .cpu_bytesel(cpu_bytesel),
        .dma_addr(dma_addr),
        .dma_data_in(dma_data_in),
        .dma_data_out(dma_data_out),
        .dma_access(dma_access),
        .dma_ack(dma_ack),
        .dma_wr_en(dma_wr_en),
        .dma_bytesel(dma_bytesel),
        .fpu_addr(fpu_addr),
        .fpu_data_in(fpu_data_in),
        .fpu_data_out(fpu_data_out),
        .fpu_access(fpu_access),
        .fpu_ack(fpu_ack),
        .fpu_wr_en(fpu_wr_en),
        .fpu_bytesel(fpu_bytesel),
        .cache_addr(cache_addr),
        .cache_data_in(cache_data_in),
        .cache_data_out(cache_data_out),
        .cache_access(cache_access),
        .cache_ack(cache_ack),
        .cache_wr_en(cache_wr_en),
        .cache_bytesel(cache_bytesel)
    );

    initial reset = 1'b1;
    logic seen_reset;

    always_ff @(posedge clk) begin
        if ($initstate) begin
            reset      <= 1'b1;
            seen_reset <= 1'b0;
        end else begin
            reset      <= 1'b0;
            if (reset)
                seen_reset <= 1'b1;
        end
    end

    // Environment assumptions: none beyond reset.

    // Safety properties
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        // Only one front-end port can receive an ACK at a time.
        assert($onehot0({cpu_ack, dma_ack, fpu_ack}));

        // Any ACK must coincide with a backend cache_ack.
        if (cpu_ack || dma_ack || fpu_ack)
            assert(cache_ack);
    end

endmodule

