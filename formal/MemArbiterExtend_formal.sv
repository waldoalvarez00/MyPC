// Formal harness for Quartus/rtl/MemArbiterExtend.sv

`default_nettype none

module MemArbiterExtend_formal(
    input logic clk
);
    // Clock and reset
    logic reset;

    // CPU bus
    (* anyseq *) logic [19:1] cpu_m_addr;
    (* anyseq *) logic [15:0] cpu_m_data_out;
    (* anyseq *) logic        cpu_m_access;
    (* anyseq *) logic        cpu_m_wr_en;
    (* anyseq *) logic [1:0]  cpu_m_bytesel;
    logic [15:0]              cpu_m_data_in;
    logic                     cpu_m_ack;

    // MCGA bus
    (* anyseq *) logic [19:1] mcga_m_addr;
    (* anyseq *) logic [15:0] mcga_m_data_out;
    (* anyseq *) logic        mcga_m_access;
    (* anyseq *) logic        mcga_m_wr_en;
    (* anyseq *) logic [1:0]  mcga_m_bytesel;
    logic [15:0]              mcga_m_data_in;
    logic                     mcga_m_ack;

    // SDRAM bus
    logic [19:1]              sdram_m_addr;
    (* anyseq *) logic [15:0] sdram_m_data_in;
    logic [15:0]              sdram_m_data_out;
    logic                     sdram_m_access;
    (* anyseq *) logic        sdram_m_ack;
    logic                     sdram_m_wr_en;
    logic [1:0]               sdram_m_bytesel;
    logic                     q_b;

    MemArbiterExtend dut (
        .clk(clk),
        .reset(reset),

        .cpu_m_addr(cpu_m_addr),
        .cpu_m_data_in(cpu_m_data_in),
        .cpu_m_data_out(cpu_m_data_out),
        .cpu_m_access(cpu_m_access),
        .cpu_m_ack(cpu_m_ack),
        .cpu_m_wr_en(cpu_m_wr_en),
        .cpu_m_bytesel(cpu_m_bytesel),

        .mcga_m_addr(mcga_m_addr),
        .mcga_m_data_in(mcga_m_data_in),
        .mcga_m_data_out(mcga_m_data_out),
        .mcga_m_access(mcga_m_access),
        .mcga_m_ack(mcga_m_ack),
        .mcga_m_wr_en(mcga_m_wr_en),
        .mcga_m_bytesel(mcga_m_bytesel),

        .sdram_m_addr(sdram_m_addr),
        .sdram_m_data_in(sdram_m_data_in),
        .sdram_m_data_out(sdram_m_data_out),
        .sdram_m_access(sdram_m_access),
        .sdram_m_ack(sdram_m_ack),
        .sdram_m_wr_en(sdram_m_wr_en),
        .sdram_m_bytesel(sdram_m_bytesel),
        .q_b(q_b)
    );

    // Reset sequencing
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

    // Environment assumption
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        if (!$past(reset) && sdram_m_ack)
            assume($past(sdram_m_access));
    end

    // Safety properties
    always_ff @(posedge clk) if (seen_reset && !reset) begin
        // Never acknowledge both CPU and MCGA in the same cycle.
        assert(!(cpu_m_ack && mcga_m_ack));

        // Any master ACK must coincide with an SDRAM ACK.
        if (cpu_m_ack)
            assert(sdram_m_ack);
        if (mcga_m_ack)
            assert(sdram_m_ack);
    end

endmodule

