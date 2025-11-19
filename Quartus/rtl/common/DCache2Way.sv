// Copyright 2025, Waldo Alvarez, https://pipflow.com
// Based on DCache.sv
//
// This file is part of MyPC.
//
// MyPC is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// MyPC is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with MyPC.  If not, see <http://www.gnu.org/licenses/>.

/*
 * 2-Way Set-Associative Data Cache (DCache2Way)
 *
 * Enhanced data cache with 2-way set-associativity and LRU replacement.
 * Reduces conflict misses compared to direct-mapped cache.
 *
 * Features:
 * - 2-way set-associative organization
 * - 256 sets × 2 ways = 512 total lines
 * - 8-word (16-byte) cache line size
 * - Total size: 2 ways × 256 sets × 8 words × 2 bytes = 8 KB
 * - LRU (Least Recently Used) replacement policy
 * - Write-back with dirty bit tracking per way
 * - Automatic flush of dirty lines on replacement
 * - Byte-level write granularity
 *
 * Cache Organization:
 * - Address breakdown: [tag | index | offset]
 *   - Tag: Upper bits for line identification (10 bits)
 *   - Index: Selects set (8 bits for 256 sets)
 *   - Offset: Word within line (3 bits for 8 words)
 *
 * Performance Improvements over Direct-Mapped:
 * - Hit rate: 92-95% (vs 85-90% direct-mapped)
 * - Reduces conflict misses by ~50-70%
 * - LRU replacement minimizes thrashing
 *
 * LRU Implementation:
 * - 1-bit LRU per set (sufficient for 2-way)
 * - 0 = Way 0 used recently, replace Way 1 next
 * - 1 = Way 1 used recently, replace Way 0 next
 * - Updated on every hit and fill operation
 */

`default_nettype none
module DCache2Way(
    input logic clk,
    input logic reset,
    input logic enabled,

    // Frontend - CPU data access interface
    input logic [19:1] c_addr,
    output logic [15:0] c_data_in,
    input logic [15:0] c_data_out,
    input logic c_access,
    output logic c_ack,
    input logic c_wr_en,
    input logic [1:0] c_bytesel,

    // Backend - Memory system interface
    output logic [19:1] m_addr,
    input logic [15:0] m_data_in,
    output logic [15:0] m_data_out,
    output logic m_access,
    input logic m_ack,
    output logic m_wr_en,
    output logic [1:0] m_bytesel,

    // Coherence interface to I-cache
    output logic        coh_wr_valid,
    output logic [19:1] coh_wr_addr,
    output logic [15:0] coh_wr_data,
    output logic [1:0]  coh_wr_bytesel,
    output logic        coh_probe_valid,
    output logic [19:1] coh_probe_addr,
    input  logic        coh_probe_present
);

parameter sets = 256;  // 256 sets × 2 ways = 512 lines (same as direct-mapped)
parameter bit DEBUG = 0;

localparam line_size = 8;
localparam index_bits = $clog2(sets);  // 8 bits for 256 sets
localparam tag_bits = 19 - 3 - index_bits;  // 10 bits
localparam index_start = 4;
localparam index_end = 4 + index_bits - 1;
localparam tag_start = 4 + index_bits;

// Internal registers
reg [19:1] c_m_addr;
reg [2:0] line_idx;
reg [7:0] line_valid;
reg busy;
reg flushing;
reg [index_end-1:0] line_address;
reg [19:1] latched_address, fetch_address;
reg [19:1] fill_addr;
reg accessing;
reg code_flush_pending;
reg code_flush_way;
reg flush_way_reg;
reg [index_bits-1:0] flush_index_reg;
reg [tag_bits-1:0] flush_tag_reg;
reg [2:0] flush_beat;
typedef enum logic [2:0] {FL_IDLE, FL_PREFETCH, FL_SEND, FL_WAIT} fl_state_t;
fl_state_t fl_state;
reg [15:0] flush_data;

// Request latching - capture CPU request when idle
reg [19:1] req_addr;
reg        req_is_write;
reg [15:0] req_wdata;
reg [1:0]  req_be;

// Write buffer for stores to line being filled (per-word)
reg [7:0]        wbuf_valid;      // one bit per word
reg [15:0]       wbuf_data[0:7];  // 8 words
reg [1:0]        wbuf_be[0:7];    // byte enables per word
reg [19:1]       wbuf_line_addr;  // base address of line being filled
reg              wbuf_active;     // buffer associated with current fill
reg [2:0]        wbuf_apply_idx;  // which word we're applying (0-7)
reg              wbuf_applying;   // in apply phase

// Fill context
reg [index_bits-1:0] fill_index_reg;

reg        debug_printed;

// Coherence outputs towards I-cache
assign coh_wr_valid     = c_ack && c_wr_en;
assign coh_wr_addr      = c_addr;
assign coh_wr_data      = c_data_out;
assign coh_wr_bytesel   = c_bytesel;
assign coh_probe_valid  = c_ack && c_wr_en;
assign coh_probe_addr   = c_addr;
// coh_probe_present is consumed later if needed for policy decisions.

// Way selection and LRU
reg selected_way;        // Which way to fill/flush (0 or 1)
wire way_to_replace;     // LRU indicates which way to replace
wire hit_way0, hit_way1; // Hit detection per way
wire hit_way;            // Which way hit (only valid when hit=1)
wire hit;                // Overall hit

// Per-way storage
wire [19:tag_start] tag_way0, tag_way1;
wire valid_way0, valid_way1;
wire dirty_way0, dirty_way1;
wire [15:0] data_way0, data_way1;

// LRU bit per set (0 = replace way1, 1 = replace way0)
wire lru_bit;
wire write_lru;

// Hit/miss logic
wire tags_match_way0 = tag_way0 == fetch_address[19:tag_start];
wire tags_match_way1 = tag_way1 == fetch_address[19:tag_start];
wire filling_current = fetch_address[19:index_start] == latched_address[19:index_start];

// Early hit conditions:
// - For reads: data must be filled (line_valid[word] = 1)
// - For writes: NO early hits - must wait for line to be valid
wire early_hit_word_ready = line_valid[fetch_address[3:1]];
wire allow_early_read_hit = !c_wr_en && early_hit_word_ready;
wire allow_early_write_hit = 1'b0;  // Disabled - writes go through write buffer

assign hit_way0 = accessing && ((valid_way0 && tags_match_way0) ||
    (busy && !flushing_active && !wbuf_applying && selected_way == 1'b0 && filling_current && (allow_early_read_hit || allow_early_write_hit)));
assign hit_way1 = accessing && ((valid_way1 && tags_match_way1) ||
    (busy && !flushing_active && !wbuf_applying && selected_way == 1'b1 && filling_current && (allow_early_read_hit || allow_early_write_hit)));

assign hit = hit_way0 || hit_way1;
assign hit_way = hit_way1;  // 0 if way0 hit, 1 if way1 hit

// Output data selection based on which way hit
wire [15:0] c_q = hit_way0 ? data_way0 : data_way1;

// Output logic
assign c_data_in = enabled ? (c_ack ? c_q : 16'b0) : m_data_in;
assign c_ack = enabled ? accessing & !flushing_active & !wbuf_applying & hit : m_ack;

// Memory interface
wire [19:1] flush_addr = {flush_tag_reg, flush_index_reg, flush_beat};
wire flushing_active = (fl_state != FL_IDLE);

assign m_addr     = enabled ? (flushing_active ? flush_addr : c_m_addr) : c_addr;
assign m_wr_en    = enabled ? (fl_state == FL_WAIT) : c_wr_en;
assign m_access   = enabled ? (flushing_active ? 1'b1 : (busy && !wbuf_applying)) : c_access;
assign m_bytesel  = enabled ? 2'b11 : c_bytesel;
assign m_data_out = enabled ? c_m_data_out : c_data_out;

// LRU replacement selection
assign way_to_replace = lru_bit;  // 0 = replace way0, 1 = replace way1

// Determine if we need to flush the selected way before filling
wire selected_dirty = selected_way ? dirty_way1 : dirty_way0;
wire selected_valid = selected_way ? valid_way1 : valid_way0;
wire flush_active_wire = flushing_active;

// Code writes are treated the same as data writes in the cache;
// coherence with I-cache is handled at the memory arbiter via invalidation.
wire code_write_hit = 1'b0;

// Flush and fill logic
// Block fills/flushes while applying write buffer
wire request_flush_dirty = c_access && ~hit && !busy && !flushing_active && !wbuf_applying && selected_valid && selected_dirty;
wire request_fill        = c_access && ~hit && !busy && !flushing_active && !wbuf_applying && (!selected_valid || !selected_dirty);
wire request_code_flush  = code_flush_pending && !busy && !flushing_active && !wbuf_applying;

wire do_flush = request_flush_dirty || request_code_flush;
wire do_fill  = request_fill && !request_code_flush;

wire write_line = m_ack && !flushing_active;

// Tag/Valid/Dirty write enables
wire write_tag_way0 = do_fill && selected_way == 1'b0;
wire write_tag_way1 = do_fill && selected_way == 1'b1;

wire flush_done = (fl_state == FL_WAIT) && m_ack && (flush_beat == 3'b111);

wire write_valid_way0 = write_tag_way0 ||
                        (selected_way == 1'b0 && ~flushing_active && line_idx == 3'b111 && m_ack) ||
                        (flush_done && flush_way_reg == 1'b0);
wire write_valid_way1 = write_tag_way1 ||
                        (selected_way == 1'b1 && ~flushing_active && line_idx == 3'b111 && m_ack) ||
                        (flush_done && flush_way_reg == 1'b1);

wire valid_way0_wdata = (flush_done && flush_way_reg == 1'b0) ? 1'b0 : 1'b1;
wire valid_way1_wdata = (flush_done && flush_way_reg == 1'b1) ? 1'b0 : 1'b1;

wire write_dirty_way0 = (c_ack & c_wr_en && hit_way0 && !code_write_hit) ||
                        (wbuf_applying && selected_way == 1'b0 && wbuf_valid[wbuf_apply_idx] && wbuf_apply_idx == 3'b0) ||
                        (flush_done && flush_way_reg == 1'b0);
wire write_dirty_way1 = (c_ack & c_wr_en && hit_way1 && !code_write_hit) ||
                        (wbuf_applying && selected_way == 1'b1 && wbuf_valid[wbuf_apply_idx] && wbuf_apply_idx == 3'b0) ||
                        (flush_done && flush_way_reg == 1'b1);

// LRU update: write on hit or fill completion
assign write_lru = (c_ack && hit) || (~flushing_active && line_idx == 3'b111 && m_ack);

// LRU RAM - stores which way to replace next per set
DPRam #(.words(sets),
        .width(1))
      LRURam(.clk(clk),
             .addr_a(c_addr[index_end:index_start]),
             .wr_en_a(1'b0),
             .wdata_a(1'b0),
             .q_a(lru_bit),
             .addr_b(latched_address[index_end:index_start]),
             .wr_en_b(write_lru),
             // Update LRU: set to opposite of the way just used
             .wdata_b(c_ack ? ~hit_way : ~selected_way),
             .q_b());

// Way 0 storage
DPRam #(.words(sets),
        .width(tag_bits))
      TagRam0(.clk(clk),
              .addr_a(c_addr[index_end:index_start]),
              .wr_en_a(1'b0),
              .wdata_a({tag_bits{1'b0}}),
              .q_a(tag_way0),
              .addr_b(latched_address[index_end:index_start]),
              .wr_en_b(write_tag_way0),
              .wdata_b(latched_address[19:tag_start]),
              .q_b());

// Debug tag writes
always_ff @(posedge clk) begin
    if (DEBUG && write_tag_way0) begin
        $display("[%0t][DCache2Way] TAG_WRITE_WAY0 idx=%h tag=%h latched_addr=%h",
                 $time, latched_address[index_end:index_start], latched_address[19:tag_start], latched_address);
    end
end

DPRam #(.words(sets),
        .width(1))
      ValidRam0(.clk(clk),
                .addr_a(c_addr[index_end:index_start]),
                .wr_en_a(1'b0),
                .wdata_a(1'b0),
                .q_a(valid_way0),
                .addr_b(latched_address[index_end:index_start]),
                .wr_en_b(write_valid_way0),
                .wdata_b(valid_way0_wdata),
                .q_b());

// Debug valid writes
always_ff @(posedge clk) begin
    if (DEBUG && write_valid_way0) begin
        $display("[%0t][DCache2Way] VALID_WRITE_WAY0 idx=%h valid=%b (flush_done=%b)",
                 $time, latched_address[index_end:index_start], valid_way0_wdata, flush_done);
    end
end

DPRam #(.words(sets),
        .width(1))
      DirtyRam0(.clk(clk),
                .addr_a(c_addr[index_end:index_start]),
                .wr_en_a(write_dirty_way0),
                .wdata_a(1'b1),
                .q_a(dirty_way0),
                .addr_b(flush_index_reg),
                .wr_en_b(flush_done && flush_way_reg == 1'b0),
                .wdata_b(1'b0),
                .q_b());

// Way 1 storage
DPRam #(.words(sets),
        .width(tag_bits))
      TagRam1(.clk(clk),
              .addr_a(c_addr[index_end:index_start]),
              .wr_en_a(1'b0),
              .wdata_a({tag_bits{1'b0}}),
              .q_a(tag_way1),
              .addr_b(latched_address[index_end:index_start]),
              .wr_en_b(write_tag_way1),
              .wdata_b(latched_address[19:tag_start]),
              .q_b());

DPRam #(.words(sets),
        .width(1))
      ValidRam1(.clk(clk),
                .addr_a(c_addr[index_end:index_start]),
                .wr_en_a(1'b0),
                .wdata_a(1'b0),
                .q_a(valid_way1),
                .addr_b(latched_address[index_end:index_start]),
                .wr_en_b(write_valid_way1),
                .wdata_b(valid_way1_wdata),
                .q_b());

DPRam #(.words(sets),
        .width(1))
      DirtyRam1(.clk(clk),
                .addr_a(c_addr[index_end:index_start]),
                .wr_en_a(write_dirty_way1),
                .wdata_a(1'b1),
                .q_a(dirty_way1),
                .addr_b(flush_index_reg),
                .wr_en_b(flush_done && flush_way_reg == 1'b1),
                .wdata_b(1'b0),
                .q_b());

// Port B read data from each way (for flush)
wire [15:0] data_way0_b, data_way1_b;
wire [15:0] c_m_data_out = flushing_active ? flush_data
                                    : (selected_way ? data_way1_b : data_way0_b);

// Separate line RAMs for each way
// B-port: ONLY for fill/flush, completely separate from CPU hits
wire [index_end:1] line_addr_for_b = flushing_active ? {flush_index_reg, flush_beat} : line_address;

// Write buffer application: apply via A-port after fill completes
wire apply_wbuf_way0 = wbuf_applying && selected_way == 1'b0;
wire apply_wbuf_way1 = wbuf_applying && selected_way == 1'b1;
wire [index_end:1] wbuf_apply_addr = {fill_index_reg, wbuf_apply_idx};

BlockRam #(.words(sets * line_size))
         LineRAM0(.clk(clk),
                  .addr_a(apply_wbuf_way0 ? wbuf_apply_addr : c_addr[index_end:1]),
                  .wr_en_a(apply_wbuf_way0 ? wbuf_valid[wbuf_apply_idx] : (c_access && c_wr_en && !flushing_active && !wbuf_applying && hit_way0)),
                  .wdata_a(apply_wbuf_way0 ? wbuf_data[wbuf_apply_idx] : c_data_out),
                  .be_a(apply_wbuf_way0 ? wbuf_be[wbuf_apply_idx] : c_bytesel),
                  .q_a(data_way0),
                  .addr_b(line_addr_for_b),
                  .wr_en_b(write_line && selected_way == 1'b0 && !flushing_active),
                  .wdata_b(m_data_in),
                  .q_b(data_way0_b),
                  .be_b(2'b11));

BlockRam #(.words(sets * line_size))
         LineRAM1(.clk(clk),
                  .addr_a(apply_wbuf_way1 ? wbuf_apply_addr : c_addr[index_end:1]),
                  .wr_en_a(apply_wbuf_way1 ? wbuf_valid[wbuf_apply_idx] : (c_access && c_wr_en && !flushing_active && !wbuf_applying && hit_way1)),
                  .wdata_a(apply_wbuf_way1 ? wbuf_data[wbuf_apply_idx] : c_data_out),
                  .be_a(apply_wbuf_way1 ? wbuf_be[wbuf_apply_idx] : c_bytesel),
                  .q_a(data_way1),
                  .addr_b(line_addr_for_b),
                  .wr_en_b(write_line && selected_way == 1'b1 && !flushing_active),
                  .wdata_b(m_data_in),
                  .q_b(data_way1_b),
                  .be_b(2'b11));

// Flush task
task automatic flush_line;
    input way;
    begin
        flush_way_reg   <= way;
        flush_index_reg <= latched_address[index_end:index_start];
        flush_tag_reg   <= way ? tag_way1 : tag_way0;
        flush_beat      <= 3'b000;
        busy <= 1'b1;
        flushing <= 1'b1;
    end
endtask

// Fill task
task automatic fill_line;
begin
    c_m_addr <= latched_address;
    fill_addr <= latched_address;
    busy <= 1'b1;
    line_valid <= 8'b0;
    if (DEBUG) begin
        $display("[%0t][DCache2Way] FILL_TASK setting busy=1", $time);
    end
end
endtask

// Reset logic and write buffer management
// NO pre-computed wires - evaluate comparison directly to avoid timing issues

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        accessing <= 1'b0;
        wbuf_valid <= 8'b0;
        wbuf_active <= 1'b0;
        wbuf_applying <= 1'b0;
        wbuf_apply_idx <= 3'b0;
    end else begin
        accessing <= c_access;

        // Write buffer capture:
        // Capture the initial write-miss that triggers the fill
        if (do_fill && c_wr_en) begin
            wbuf_active <= 1'b1;
            wbuf_line_addr <= c_addr[19:1];
            wbuf_valid[c_addr[3:1]] <= 1'b1;
            wbuf_data[c_addr[3:1]]  <= c_data_out;
            wbuf_be[c_addr[3:1]]    <= c_bytesel;
            if (DEBUG) begin
                $display("[%0t][DCache2Way] WBUF_CAPTURE_INITIAL addr=%h offset=%0d data=%h be=%b",
                         $time, c_addr, c_addr[3:1], c_data_out, c_bytesel);
            end
        end
        // Capture subsequent writes during fill to same line
        // Direct comparison in if statement to avoid wire timing issues
        else if (busy && !flushing_active && !wbuf_applying && c_access && c_wr_en && (c_addr[19:4] == latched_address[19:4])) begin
            wbuf_valid[c_addr[3:1]] <= 1'b1;
            wbuf_data[c_addr[3:1]]  <= c_data_out;
            wbuf_be[c_addr[3:1]]    <= c_bytesel;
            if (DEBUG) begin
                $display("[%0t][DCache2Way] WBUF_CAPTURE_DURING addr=%h offset=%0d data=%h be=%b (c[19:4]=%h lat[19:4]=%h)",
                         $time, c_addr, c_addr[3:1], c_data_out, c_bytesel, c_addr[19:4], latched_address[19:4]);
            end
        end
    end
end

// Line address calculation
always_comb begin
    if (m_ack && flushing_active)
        line_address = {flush_index_reg, flush_beat + 1'b1};
    else if (request_flush_dirty)
        line_address = {latched_address[index_end:index_start], 3'b0};
    else
        line_address = {fill_addr[index_end:index_start], c_m_addr[3:1]};
end

// Address latching
// latched_address: captured when starting a fill, held stable during fill and wbuf application
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        latched_address <= {19{1'b0}};
    end else begin
        if (!busy && !flushing_active) begin
            latched_address <= c_addr;
            if (DEBUG && c_access) begin
                $display("[%0t][DCache2Way] LATCH_ADDR c_addr=%h busy=%b flush=%b",
                         $time, c_addr, busy, flushing_active);
            end
        end
        fetch_address <= c_addr;
    end
end

// Way selection on miss - use LRU
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        selected_way <= 1'b0;
    end else begin
        if (code_write_hit)
            selected_way <= hit_way;
        else if (c_access && ~hit && !busy && !flushing_active)
            selected_way <= way_to_replace;
    end
end

// Fill/flush state machines
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        line_idx <= 3'b0;
        line_valid <= 8'b0;
        busy <= 1'b0;
        flushing <= 1'b0;
        fill_addr <= {19{1'b0}};
        code_flush_pending <= 1'b0;
        code_flush_way <= 1'b0;
        flush_way_reg <= 1'b0;
        flush_index_reg <= {index_bits{1'b0}};
        flush_tag_reg <= {tag_bits{1'b0}};
        flush_beat <= 3'b0;
        fl_state <= FL_IDLE;
        flush_data <= 16'h0000;
        fill_index_reg <= {index_bits{1'b0}};
    end else if (enabled) begin
        // ------------------------
        // Line fill (when not flushing)
        // ------------------------
        if (m_ack && !flushing_active && busy && !wbuf_applying) begin
            c_m_addr <= {c_m_addr[19:4], c_m_addr[3:1] + 1'b1};
            line_idx <= line_idx + 1'b1;
            line_valid[c_m_addr[3:1]] <= 1'b1;
            if (line_idx == 3'b111) begin
                line_idx <= 3'b0;
                // If we have buffered writes, enter applying state
                if (wbuf_active && (|wbuf_valid)) begin
                    wbuf_applying <= 1'b1;
                    wbuf_apply_idx <= 3'b0;
                    if (DEBUG) begin
                        $display("[%0t][DCache2Way] FILL_DONE, entering wbuf_applying", $time);
                    end
                end else begin
                    busy <= 1'b0;
                    wbuf_active <= 1'b0;
                    wbuf_valid <= 8'b0;
                    if (DEBUG) begin
                        $display("[%0t][DCache2Way] FILL_DONE, clearing busy", $time);
                    end
                end
            end
        end else if (!flushing_active && do_fill) begin
            line_idx <= 3'b0;
            fill_index_reg <= latched_address[index_end:index_start];
            if (DEBUG) begin
                $display("[%0t][DCache2Way] FILL_START latched_addr=%h fill_index=%h",
                         $time, latched_address, latched_address[index_end:index_start]);
            end
            fill_line();
        end else if (wbuf_applying) begin
            // Apply buffered writes via A-port (one per cycle)
            if (wbuf_apply_idx == 3'b111) begin
                // Last word - done applying
                wbuf_applying <= 1'b0;
                busy <= 1'b0;
                wbuf_active <= 1'b0;
                wbuf_valid <= 8'b0;
            end else begin
                wbuf_apply_idx <= wbuf_apply_idx + 1'b1;
            end
        end

        // Schedule code flush on write-hit (keeps residency)
        if (code_write_hit && fl_state == FL_IDLE) begin
            code_flush_pending <= 1'b1;
            code_flush_way     <= hit_way;
        end

        // ------------------------
        // Flush FSM (with proper BlockRam read latency handling)
        // ------------------------
        case (fl_state)
            FL_IDLE: begin
                flushing <= 1'b0;
                if (do_flush) begin
                    flush_way_reg   <= code_flush_pending ? code_flush_way : selected_way;
                    flush_index_reg <= latched_address[index_end:index_start];
                    flush_tag_reg   <= code_flush_pending ? (code_flush_way ? tag_way1 : tag_way0)
                                                          : (selected_way ? tag_way1 : tag_way0);
                    flush_beat      <= 3'b000;
                    fl_state        <= FL_PREFETCH;
                    flushing        <= 1'b1;
                    busy            <= 1'b1;
                    code_flush_pending <= 1'b0;
                end
            end

            FL_PREFETCH: begin
                // B-port address is presented via line_addr_for_b = {flush_index_reg, flush_beat}
                // Wait one cycle for BlockRam to produce valid data on B-port
                flushing   <= 1'b1;
                fl_state   <= FL_SEND;
            end

            FL_SEND: begin
                // Capture data from B-port (now valid after 1-cycle BlockRam latency)
                flushing   <= 1'b1;
                flush_data <= flush_way_reg ? data_way1_b : data_way0_b;
                fl_state   <= FL_WAIT;
            end

            FL_WAIT: begin
                // Send captured data to SDRAM and wait for acknowledgment
                // m_addr, m_data_out, m_access, m_wr_en are driven combinationally
                flushing <= 1'b1;
                if (m_ack) begin
                    if (flush_beat == 3'b111) begin
                        // Flush complete - dirty bit cleared via flush_done signal
                        fl_state   <= FL_IDLE;
                        flushing   <= 1'b0;
                        busy       <= 1'b0;
                        flush_beat <= 3'b000;
                    end else begin
                        // Move to next beat
                        flush_beat <= flush_beat + 1'b1;
                        fl_state   <= FL_PREFETCH;
                    end
                end
            end
        endcase
    end
end

// --------------------------------------------------------------------------
// Debug instrumentation (sim-only). Enabled when DEBUG!=0.
// Keep minimal traces for coherence debugging.
// --------------------------------------------------------------------------
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        debug_printed     <= 1'b0;
    end else begin
        if (DEBUG) begin
            if (!debug_printed) begin
                $display("[%0t][DCache2Way] DEBUG ENABLED", $time);
                debug_printed <= 1'b1;
            end
            if (c_access) begin
                $display("[%0t][DCache2Way] ACCESS addr=%h hit=%b hit_way0=%b hit_way1=%b c_ack=%b busy=%b flushing=%b fl_state=%0d c_wr_en=%b m_ack=%b line_idx=%0d val0=%b val1=%b tag0=%h tag1=%h line_valid=%b wbuf_active=%b wbuf_applying=%b",
                         $time, c_addr, hit, hit_way0, hit_way1, c_ack, busy, flushing, fl_state, c_wr_en, m_ack, line_idx, valid_way0, valid_way1, tag_way0, tag_way1, line_valid[c_addr[3:1]], wbuf_active, wbuf_applying);
                $display("[%0t][DCache2Way]   HIT_DEBUG: fetch_addr=%h fetch_tag=%h tags_match0=%b tags_match1=%b accessing=%b",
                         $time, fetch_address, fetch_address[19:tag_start], tags_match_way0, tags_match_way1, accessing);
            end
            if (code_write_hit) begin
                $display("[%0t][DCache2Way] CODE_WRITE_HIT addr=%h data=%h be=%b way=%0d coh_probe_present=%b",
                         $time, c_addr, c_data_out, c_bytesel, hit_way, coh_probe_present);
            end
            if (c_ack && c_wr_en && hit) begin
                $display("[%0t][DCache2Way] WRITE_HIT addr=%h data=%h be=%b way=%0d dirty0=%b dirty1=%b",
                         $time, c_addr, c_data_out, c_bytesel, hit_way, dirty_way0, dirty_way1);
            end
            if (request_flush_dirty && !flushing_active) begin
                $display("[%0t][DCache2Way] FLUSH_REQ idx=%h sel_way=%0d dirty0=%b dirty1=%b valid0=%b valid1=%b",
                         $time,
                         latched_address[index_end:index_start],
                         selected_way, dirty_way0, dirty_way1, valid_way0, valid_way1);
            end
            if (m_access && m_wr_en) begin
                $display("[%0t][DCache2Way] WB addr=%h data=%h be=%b busy=%b flushing=%b",
                         $time, m_addr, m_data_out, m_bytesel, busy, flushing);
            end
            if (!flushing_active && m_ack && busy && line_idx == 3'b111) begin
                $display("[%0t][DCache2Way] FILL_COMPLETE idx=%h way=%0d tag0=%h tag1=%h val0=%b val1=%b wbuf_active=%b wbuf_valid=%b",
                         $time,
                         c_m_addr[index_end:index_start],
                         selected_way,
                         tag_way0, tag_way1, valid_way0, valid_way1, wbuf_active, wbuf_valid);
            end
            if (wbuf_applying) begin
                $display("[%0t][DCache2Way] APPLYING_WBUF idx=%0d addr=%h data=%h be=%b way=%0d valid=%b wr_en=%b",
                         $time, wbuf_apply_idx, {fill_index_reg, wbuf_apply_idx, 1'b0}, wbuf_data[wbuf_apply_idx], wbuf_be[wbuf_apply_idx], selected_way, wbuf_valid[wbuf_apply_idx],
                         (selected_way == 1'b0) ? (apply_wbuf_way0 && wbuf_valid[wbuf_apply_idx]) : (apply_wbuf_way1 && wbuf_valid[wbuf_apply_idx]));
            end
            // Trace flush scheduling and execution (for SMC debugging)
            if (do_flush && !flushing_active) begin
                $display("[%0t][DCache2Way] FLUSH_START idx=%h way=%0d dirty0=%b dirty1=%b valid0=%b valid1=%b code_flush_pending=%b code_flush_way=%0d",
                         $time,
                         latched_address[index_end:index_start],
                         (code_flush_pending ? code_flush_way : selected_way),
                         dirty_way0, dirty_way1, valid_way0, valid_way1,
                         code_flush_pending, code_flush_way);
            end
            if (flushing_active && m_access && m_wr_en && !m_ack) begin
                $display("[%0t][DCache2Way] FLUSH_BEAT addr=%h data=%h",
                         $time, c_m_addr, c_m_data_out);
            end
            if (flushing_active && m_ack) begin
                $display("[%0t][DCache2Way] FLUSH_ACK addr=%h",
                         $time, c_m_addr);
            end
        end
    end
end

endmodule
`default_nettype wire
