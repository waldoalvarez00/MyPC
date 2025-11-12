// Copyright 2025, Waldo Alvarez
// 2-Way Set-Associative Instruction Cache (without prefetch)
// Simpler and more reliable implementation

`default_nettype none
module ICache2Way(
    input logic clk,
    input logic reset,
    input logic enabled,

    // Frontend - CPU instruction fetch interface
    input logic [19:1] c_addr,
    output logic [15:0] c_data_in,
    input logic c_access,
    output logic c_ack,

    // Backend - Memory system interface
    output logic [19:1] m_addr,
    input logic [15:0] m_data_in,
    output logic m_access,
    input logic m_ack
);

parameter sets = 256;

localparam line_size = 8;
localparam index_bits = $clog2(sets);
localparam tag_bits = 19 - 3 - index_bits;
localparam index_start = 4;
localparam index_end = 4 + index_bits - 1;
localparam tag_start = 4 + index_bits;

// Internal registers
reg [19:1] c_m_addr;
reg [2:0] line_idx;
reg [7:0] line_valid;
reg busy;
reg [index_end-1:0] line_address;
reg [19:1] latched_address, fetch_address;
reg updating;
reg accessing;

// Way selection and LRU
reg selected_way;
wire way_to_replace;
wire hit_way0, hit_way1;
wire hit_way;
wire hit;

// Per-way storage
wire [19:tag_start] tag_way0, tag_way1;
wire valid_way0, valid_way1;
wire [15:0] data_way0, data_way1;

// LRU bit per set
wire lru_bit;
wire write_lru;

// Hit/miss logic
wire tags_match_way0 = tag_way0 == fetch_address[19:tag_start];
wire tags_match_way1 = tag_way1 == fetch_address[19:tag_start];
wire filling_current = fetch_address[19:index_start] == latched_address[19:index_start];

assign hit_way0 = accessing && ((valid_way0 && tags_match_way0) ||
    (busy && selected_way == 1'b0 && filling_current && line_valid[fetch_address[3:1]]));
assign hit_way1 = accessing && ((valid_way1 && tags_match_way1) ||
    (busy && selected_way == 1'b1 && filling_current && line_valid[fetch_address[3:1]]));

assign hit = hit_way0 || hit_way1;
assign hit_way = hit_way1;

// Output data selection
wire [15:0] c_q = hit_way0 ? data_way0 : data_way1;

assign c_data_in = enabled ? (c_ack ? c_q : 16'b0) : m_data_in;
assign c_ack = enabled ? accessing & hit : m_ack;

assign m_addr = enabled ? c_m_addr : c_addr;
assign m_access = enabled ? busy & ~m_ack : c_access;

wire do_fill = updating && ~hit && !busy;
wire write_line = m_ack;

wire write_tag_way0 = do_fill && selected_way == 1'b0;
wire write_tag_way1 = do_fill && selected_way == 1'b1;

wire write_valid_way0 = write_tag_way0 || (selected_way == 1'b0 && line_idx == 3'b111 && m_ack);
wire write_valid_way1 = write_tag_way1 || (selected_way == 1'b1 && line_idx == 3'b111 && m_ack);

assign write_lru = (c_ack && hit) || (line_idx == 3'b111 && m_ack);
assign way_to_replace = lru_bit;

// LRU RAM
DPRam #(.words(sets), .width(1))
  LRURam(.clk(clk),
         .addr_a(c_addr[index_end:index_start]),
         .wr_en_a(1'b0),
         .wdata_a(1'b0),
         .q_a(lru_bit),
         .addr_b(latched_address[index_end:index_start]),
         .wr_en_b(write_lru),
         .wdata_b(c_ack ? ~hit_way : ~selected_way),
         .q_b());

// Way 0 storage
DPRam #(.words(sets), .width(tag_bits))
  TagRam0(.clk(clk),
          .addr_a(c_addr[index_end:index_start]),
          .wr_en_a(1'b0),
          .wdata_a({tag_bits{1'b0}}),
          .q_a(tag_way0),
          .addr_b(latched_address[index_end:index_start]),
          .wr_en_b(write_tag_way0),
          .wdata_b(latched_address[19:tag_start]),
          .q_b());

DPRam #(.words(sets), .width(1))
  ValidRam0(.clk(clk),
            .addr_a(c_addr[index_end:index_start]),
            .wr_en_a(1'b0),
            .wdata_a(1'b0),
            .q_a(valid_way0),
            .addr_b(latched_address[index_end:index_start]),
            .wr_en_b(write_valid_way0),
            .wdata_b(selected_way == 1'b0 && line_idx == 3'b111),
            .q_b());

// Way 1 storage
DPRam #(.words(sets), .width(tag_bits))
  TagRam1(.clk(clk),
          .addr_a(c_addr[index_end:index_start]),
          .wr_en_a(1'b0),
          .wdata_a({tag_bits{1'b0}}),
          .q_a(tag_way1),
          .addr_b(latched_address[index_end:index_start]),
          .wr_en_b(write_tag_way1),
          .wdata_b(latched_address[19:tag_start]),
          .q_b());

DPRam #(.words(sets), .width(1))
  ValidRam1(.clk(clk),
            .addr_a(c_addr[index_end:index_start]),
            .wr_en_a(1'b0),
            .wdata_a(1'b0),
            .q_a(valid_way1),
            .addr_b(latched_address[index_end:index_start]),
            .wr_en_b(write_valid_way1),
            .wdata_b(selected_way == 1'b1 && line_idx == 3'b111),
            .q_b());

// Line RAMs
BlockRam #(.words(sets * line_size))
  LineRAM0(.clk(clk),
          .addr_a(c_addr[index_end:1]),
          .wr_en_a(1'b0),
          .wdata_a(16'b0),
          .be_a(2'b11),
          .q_a(data_way0),
          .addr_b(line_address),
          .wr_en_b(write_line && selected_way == 1'b0),
          .wdata_b(m_data_in),
          .q_b(),
          .be_b(2'b11));

BlockRam #(.words(sets * line_size))
  LineRAM1(.clk(clk),
          .addr_a(c_addr[index_end:1]),
          .wr_en_a(1'b0),
          .wdata_a(16'b0),
          .be_a(2'b11),
          .q_a(data_way1),
          .addr_b(line_address),
          .wr_en_b(write_line && selected_way == 1'b1),
          .wdata_b(m_data_in),
          .q_b(),
          .be_b(2'b11));

task automatic fill_line;
begin
    c_m_addr <= c_addr;
    busy <= 1'b1;
    line_valid <= 8'b0;
end
endtask

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        accessing <= 1'b0;
    end else begin
        accessing <= c_access;
    end
end

always_comb begin
    line_address = {latched_address[index_end:index_start], c_m_addr[3:1]};
end

always_ff @(posedge clk) begin
    if (!busy)
        latched_address <= c_addr;
    fetch_address <= c_addr;
end

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        selected_way <= 1'b0;
    end else begin
        if (updating && ~hit && !busy)
            selected_way <= way_to_replace;
    end
end

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        updating <= 1'b0;
    end else begin
        if (enabled && !busy && c_access)
            updating <= 1'b1;
        if (updating && !busy)
            updating <= 1'b0;
    end
end

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        line_idx <= 3'b0;
        line_valid <= 8'b0;
        busy <= 1'b0;
    end else if (enabled && m_ack) begin
        c_m_addr <= {c_m_addr[19:4], c_m_addr[3:1] + 1'b1};
        line_idx <= line_idx + 1'b1;
        line_valid[c_m_addr[3:1]] <= 1'b1;
        if (line_idx == 3'b111) begin
            busy <= 1'b0;
        end
    end else if (enabled && do_fill) begin
        fill_line();
    end
end

endmodule
`default_nettype wire
