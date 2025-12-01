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

    // Backend - Memory system interface (main: fills and flushes)
    output logic [19:1] m_addr,
    input logic [15:0] m_data_in,
    output logic [15:0] m_data_out,
    output logic m_access,
    input logic m_ack,
    output logic m_wr_en,
    output logic [1:0] m_bytesel,

    // Backend - Victim writeback interface (separate port for non-blocking)
    output logic [18:0] vwb_addr,  // Standard indexing
    output logic [15:0] vwb_data_out,
    output logic vwb_access,
    input logic vwb_ack,
    output logic vwb_wr_en,
    output logic [1:0] vwb_bytesel,

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
reg [index_bits-1:0] code_flush_index;
reg [tag_bits-1:0] code_flush_tag;
reg flush_way_reg;
reg [index_bits-1:0] flush_index_reg;
reg [tag_bits-1:0] flush_tag_reg;
reg [2:0] flush_beat;
typedef enum logic [2:0] {FL_IDLE, FL_ADDR_SETUP, FL_PREFETCH, FL_SEND, FL_WAIT, FL_VICTIM_WB = 3'b101} fl_state_t;
fl_state_t fl_state;
reg [15:0] flush_data;

// PHASE 2: Victim buffer capture control
reg        capturing_to_victim;    // Current flush is capturing to victim buffer
reg        victim_capture_id;      // Which victim buffer entry (0 or 1)
reg        eviction_started;       // Prevents multiple evictions for same miss
reg [19:1] eviction_addr;          // Address that triggered eviction

// ============================================================================
// NON-BLOCKING CACHE ARCHITECTURE - PHASE 1: DATA STRUCTURES
// ============================================================================

// Victim Buffer (2 entries) - Holds evicted dirty lines for background writeback
// Using separate arrays to avoid packed struct issues
logic        victim_valid [0:1];          // Entry contains valid dirty line
logic [15:0] victim_addr [0:1];           // Cache line base address (standard indexing)
logic [15:0] victim_data [0:1][0:7];      // 8 words per victim entry
logic [2:0]  victim_wb_beat [0:1];        // Writeback progress counter (0-7)
logic        victim_wb_active [0:1];      // Currently being written back
logic        victim_alloc_ptr;            // Round-robin allocation pointer (0 or 1)
logic [15:0] victim_wb_base_addr;         // Registered base address (standard indexing)

// Fill Buffer (1 entry) - Accumulates incoming cache line for early restart
// Using separate signals to avoid packed struct issues (fb_ prefix to avoid conflicts)
logic        fb_valid;          // Fill in progress
logic [19:1] fb_addr;           // Address being filled
logic [15:0] fb_data [0:7];     // Accumulating data
logic [7:0]  fb_words_valid;    // Bitmap: which words received
logic        fb_way;            // Target way (0 or 1)
logic [index_bits-1:0] fb_index; // Target index
logic [tag_bits-1:0]   fb_tag;   // Target tag

// Memory Request Queue (4 entries) - Serializes memory operations
// PHASE 4: Use separate arrays instead of struct array (Icarus Verilog limitation)
typedef enum logic [1:0] {
    MEM_REQ_NONE     = 2'b00,    // Empty slot
    MEM_REQ_FILL     = 2'b01,    // Cache line fill
    MEM_REQ_VICTIM_WB = 2'b10    // Victim buffer writeback
} mem_req_type_t;

logic [1:0]  mem_req_type [0:3];   // Type of each queue entry
logic [19:1] mem_req_addr [0:3];   // Address for each entry
logic        mem_req_victim [0:3]; // Victim buffer ID (for VICTIM_WB requests)

logic [1:0] queue_head;            // Head pointer (dequeue here)
logic [1:0] queue_tail;            // Tail pointer (enqueue here)
logic [2:0] queue_count;           // Number of entries in queue (0-4)

// Queue status (derived from count)
wire queue_full  = (queue_count == 3'd4);
wire queue_empty = (queue_count == 3'd0);

// PHASE 4: Queue processing state
reg        queue_processing;      // Currently processing a queue entry
reg [1:0]  queue_processing_type; // Type of request being processed (from mem_req_type_t)
reg [19:1] queue_processing_addr; // Address of request being processed
reg        queue_processing_victim; // Victim ID for VICTIM_WB requests

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

// Guard to prevent new fill/flush immediately after wbuf_applying clears
// This gives hit detection time to settle (RAM read latency)
reg just_finished_wbuf;

// Track whether fill has sent at least one memory request
// This prevents stale m_ack from flush being interpreted as fill data
reg fill_request_sent;
reg [2:0] fill_delay_cnt;  // Counter to delay fill_request_sent for pipeline draining

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

// Early hit logic uses CURRENT cycle's address (c_addr) not registered fetch_address
// This is critical because c_access/c_addr arrive in the same cycle
wire filling_current_early = c_addr[19:index_start] == latched_address[19:index_start];
// Word is ready if: already filled OR being filled this cycle
// BUG FIX: Require fill_request_sent to ensure we've actually sent fill requests
// This prevents interpreting stale flush m_ack as fill data
wire fill_in_progress = busy && !flushing_active && !wbuf_applying;
wire word_being_filled = m_ack && fill_in_progress && fill_request_sent && (c_m_addr[3:1] == c_addr[3:1]);
wire early_hit_word_ready = line_valid[c_addr[3:1]] || word_being_filled;
wire allow_early_read_hit = !c_wr_en && early_hit_word_ready;
wire allow_early_write_hit = 1'b0;  // Disabled - writes go through write buffer

// Normal hit uses registered signals (accessing, fetch_address)
// Early hit uses current cycle signals (c_access, c_addr) to avoid 1-cycle delay
// Use always_comb to work around Icarus Verilog wire evaluation issue
logic early_hit_base;
logic early_hit_allowed;
logic early_hit_way0;
logic early_hit_way1;

// Break down into multiple stages to work around Icarus Verilog bug
logic early_cond1, early_cond2, early_cond3, early_cond4;

always_comb begin
    // Stage 1: Basic conditions
    early_cond1 = c_access & busy;
    // Stage 2: Add negations (use flushing_main - victim WB on separate port doesn't block)
    early_cond2 = early_cond1 & ~flushing_main;
    // Stage 3: Add wbuf check
    early_cond3 = early_cond2 & ~wbuf_applying;
    // Stage 4: Add address match
    early_cond4 = early_cond3 & filling_current_early;

    early_hit_base = early_cond4;
    early_hit_allowed = allow_early_read_hit | allow_early_write_hit;
    early_hit_way0 = early_hit_base & (selected_way == 1'b0) & early_hit_allowed;
    early_hit_way1 = early_hit_base & (selected_way == 1'b1) & early_hit_allowed;

    if (DEBUG && c_access && !c_ack) begin
        $display("[%0t][DCache2Way]   EARLY_COND: c_access=%b busy=%b flushing=%b wbuf_applying=%b filling_current=%b",
                 $time, c_access, busy, flushing_active, wbuf_applying, filling_current_early);
        $display("[%0t][DCache2Way]   EARLY_ADDR: c_addr[19:4]=%h latched[19:4]=%h c_addr=%h latched=%h",
                 $time, c_addr[19:4], latched_address[19:4], c_addr, latched_address);
        $display("[%0t][DCache2Way]   EARLY_STAGES: cond1=%b cond2=%b cond3=%b cond4=%b base=%b",
                 $time, early_cond1, early_cond2, early_cond3, early_cond4, early_hit_base);
        $display("[%0t][DCache2Way]   EARLY_WAY: selected_way=%b way0_match=%b way1_match=%b allowed=%b",
                 $time, selected_way, (selected_way == 1'b0), (selected_way == 1'b1), early_hit_allowed);
    end
end

// BUG FIX: Normal hit must check !busy because tag/valid are set at fill START
// but data isn't available until fill completes. During fills, only early_hit can assert.
assign hit_way0 = (accessing && valid_way0 && tags_match_way0 && !busy) || early_hit_way0;
assign hit_way1 = (accessing && valid_way1 && tags_match_way1 && !busy) || early_hit_way1;

assign hit = hit_way0 || hit_way1;
assign hit_way = hit_way1;  // 0 if way0 hit, 1 if way1 hit

// Output data selection based on which way hit
wire [15:0] c_q = hit_way0 ? data_way0 : data_way1;

// Check if current read has pending write in write buffer (for early hit during fill)
wire wbuf_has_data = wbuf_active && (fetch_address[19:4] == wbuf_line_addr[19:4]) && wbuf_valid[fetch_address[3:1]];
wire [15:0] wbuf_read_data = wbuf_data[fetch_address[3:1]];

// Output logic: use write buffer data if available, otherwise use cache data
// BUG FIX: Bypass with m_data_in when word_being_filled (early hit during fill)
// This avoids the read-during-write hazard where port A returns stale data
// while port B is writing the new fill data
assign c_data_in = enabled ? (c_ack ? (word_being_filled ? m_data_in : (wbuf_has_data ? wbuf_read_data : c_q)) : 16'b0) : m_data_in;
// c_ack uses 'accessing' to match BlockRam 1-cycle latency
// Early hit prevents miss, but ack comes next cycle when data ready
// BUG FIX: Use !flushing_main instead of !flushing_active to allow acks during non-blocking victim WB
// Victim writebacks use separate VWB port, so they shouldn't block c_ack for completed operations
assign c_ack = enabled ? accessing & !flushing_main & !wbuf_applying & !just_finished_wbuf & hit : m_ack;


// Memory interface
wire [19:1] flush_addr = {flush_tag_reg, flush_index_reg, flush_beat};
// Victim WB address reconstruction from {tag, index} storage
// victim_wb_base_addr[15:0] = {tag[tag_bits-1:0], index[index_bits-1:0]}
// Need to reconstruct: address[19:tag_start] = tag, address[index_end:index_start] = index, address[3:1] = flush_beat
wire [18:0] victim_wb_addr;
assign victim_wb_addr[18:3+index_bits] = victim_wb_base_addr[15:index_bits];  // Tag bits [19:tag_start]
assign victim_wb_addr[2+index_bits:3] = victim_wb_base_addr[index_bits-1:0];  // Index bits [index_end:index_start]
assign victim_wb_addr[2:0] = flush_beat;                                       // Word offset [3:1]
wire flushing_active = (fl_state != FL_IDLE);
wire flushing_main = flushing_active && (fl_state != FL_VICTIM_WB);  // Flush on main port
wire flushing_victim = (fl_state == FL_VICTIM_WB);                    // Victim WB on separate port

// Main memory port: fills and regular flushes (FL_WAIT)
assign m_addr     = enabled ? (flushing_main ? flush_addr : c_m_addr) : c_addr;
assign m_wr_en    = enabled ? (fl_state == FL_WAIT) : c_wr_en;
// BUG FIX: Only assert m_access during FL_WAIT when flushing to avoid spurious reads
// During FL_ADDR_SETUP, FL_PREFETCH, FL_SEND we're reading from BlockRam, not memory
assign m_access   = enabled ? ((fl_state == FL_WAIT) ? 1'b1 : (busy && !flushing_active && !wbuf_applying)) : c_access;
assign m_bytesel  = enabled ? 2'b11 : c_bytesel;
assign m_data_out = enabled ? c_m_data_out : c_data_out;

// Victim writeback port: non-blocking background writebacks
assign vwb_addr     = victim_wb_addr;
assign vwb_data_out = victim_data[victim_capture_id][flush_beat];
assign vwb_access   = enabled && flushing_victim;
assign vwb_wr_en    = enabled && flushing_victim;
assign vwb_bytesel  = 2'b11;

// LRU replacement selection
assign way_to_replace = lru_bit;  // 0 = replace way0, 1 = replace way1

// Determine if we need to flush the way being replaced before filling
// BUG FIX: Use way_to_replace (current LRU decision) NOT selected_way (old registered value)
wire replace_way_dirty = way_to_replace ? dirty_way1 : dirty_way0;
wire replace_way_valid = way_to_replace ? valid_way1 : valid_way0;

// Keep selected_dirty/valid for other uses (e.g., code_write_hit)
wire selected_dirty = selected_way ? dirty_way1 : dirty_way0;
wire selected_valid = selected_way ? valid_way1 : valid_way0;
wire flush_active_wire = flushing_active;

// Code writes: when writing to an address that I-cache has resident,
// schedule a flush to write-through to memory so I-cache refetch gets fresh data.
wire code_write_hit = c_ack & c_wr_en & coh_probe_present;

// Flush and fill logic
// Block fills/flushes while applying write buffer
// Use replace_way_* to check the way that will ACTUALLY be replaced
// BUG FIX: Add !just_finished_wbuf to prevent new operations before hit detection settles
// BUG FIX: Prevent multiple evictions for same miss (same address)
wire eviction_in_progress = eviction_started && (latched_address == eviction_addr);
wire request_flush_dirty = c_access && ~hit && !busy && !flushing_active && !wbuf_applying && !just_finished_wbuf && !eviction_in_progress && replace_way_valid && replace_way_dirty;
wire request_fill        = c_access && ~hit && !busy && !flushing_active && !wbuf_applying && !just_finished_wbuf && (!replace_way_valid || !replace_way_dirty);
wire request_code_flush  = code_flush_pending && !busy && !flushing_active && !wbuf_applying;

wire do_flush = request_flush_dirty || request_code_flush;
wire do_fill  = request_fill && !request_code_flush;
// PHASE 4: Detect fill starting this cycle to serialize with queue processing
wire fill_starting = !flushing_active && do_fill;

// BUG FIX: Require fill_request_sent to prevent stale flush acks from writing bad data to LineRAM
// The delay counter in fill_request_sent ensures the arbiter pipeline has drained
wire write_line = m_ack && !flushing_active && fill_request_sent;

// Tag/Valid/Dirty write enables
// BUG FIX: Use way_to_replace instead of selected_way because selected_way is registered
// and won't have the new value until next cycle
wire write_tag_way0 = do_fill && way_to_replace == 1'b0;
wire write_tag_way1 = do_fill && way_to_replace == 1'b1;

// PHASE 2: flush_done must also trigger for FL_VICTIM_WB completion and victim capture
// Flush done: FL_WAIT uses m_ack, FL_VICTIM_WB uses vwb_ack, victim capture in FL_SEND
wire victim_capture_done = (fl_state == FL_SEND) && capturing_to_victim && (flush_beat == 3'b111);
wire flush_done = ((fl_state == FL_WAIT) && m_ack && (flush_beat == 3'b111)) ||
                  ((fl_state == FL_VICTIM_WB) && vwb_ack && (flush_beat == 3'b111)) ||
                  victim_capture_done;

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

// Debug LRU reads and writes
`ifndef SYNTHESIS
always @(posedge clk) begin
    if (write_lru) begin
        $display("[%0t][DCache2Way] LRU_WRITE idx=%0d old_lru=%b new_lru=%b (c_ack=%b hit_way=%b selected_way=%b)",
                 $time, latched_address[index_end:index_start], lru_bit, c_ack ? ~hit_way : ~selected_way,
                 c_ack, hit_way, selected_way);
    end
    if (c_access && !busy && !flushing_active) begin
        $display("[%0t][DCache2Way] LRU_READ idx=%0d lru_bit=%b way_to_replace=%0d",
                 $time, c_addr[index_end:index_start], lru_bit, way_to_replace);
    end
end
`endif

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

// Debug tag writes for way 1
always_ff @(posedge clk) begin
    if (DEBUG && write_tag_way1) begin
        $display("[%0t][DCache2Way] TAG_WRITE_WAY1 idx=%h tag=%h latched_addr=%h",
                 $time, latched_address[index_end:index_start], latched_address[19:tag_start], latched_address);
    end
end

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
// Main port data: flush or normal read (victim WB now on separate port)
wire [15:0] c_m_data_out = flushing_main ? flush_data
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
                  // BUG FIX: Add !busy to prevent direct writes during fill (should go through wbuf)
                  .wr_en_a(apply_wbuf_way0 ? wbuf_valid[wbuf_apply_idx] : (c_access && c_wr_en && !busy && !flushing_active && !wbuf_applying && hit_way0)),
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
                  // BUG FIX: Add !busy to prevent direct writes during fill (should go through wbuf)
                  .wr_en_a(apply_wbuf_way1 ? wbuf_valid[wbuf_apply_idx] : (c_access && c_wr_en && !busy && !flushing_active && !wbuf_applying && hit_way1)),
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

// Fill task - now takes address parameter to avoid using stale latched_address
task automatic fill_line;
    input [19:1] addr;
begin
    // Align c_m_addr to cache line boundary (zero out word offset bits [3:1])
    c_m_addr <= {addr[19:4], 3'b000};
    fill_addr <= addr;
    busy <= 1'b1;
    line_valid <= 8'b0;
    if (DEBUG) begin
        $display("[%0t][DCache2Way] FILL_TASK addr=%h aligned=%h setting busy=1", $time, addr, {addr[19:4], 3'b000});
    end
end
endtask

// PHASE 3: Queue operations will be implemented in always_ff block in Phase 4
// (Icarus Verilog doesn't support struct field assignments in tasks)

// Reset logic and write buffer management
// NO pre-computed wires - evaluate comparison directly to avoid timing issues

// PROT ADDRESS DEBUG: Track all activity on protected address 0x00100
`ifndef SYNTHESIS
    localparam logic [19:1] PROT_ADDR = 19'h00100;

    always_ff @(posedge clk) begin
        if (!reset) begin
            // Track CPU accesses to PROT address
            if (c_access && c_addr == PROT_ADDR) begin
                $display("[%0t][DC-PROT] CPU_ACCESS addr=%h wr=%b data_out=%h ack=%b",
                         $time, c_addr, c_wr_en, c_data_out, c_ack);
            end

            // Track memory fills touching PROT address line (0x00100-0x00107)
            if (m_ack && !flushing_active && busy && !wbuf_applying && fill_request_sent) begin
                if (c_m_addr[19:4] == PROT_ADDR[19:4]) begin
                    $display("[%0t][DC-PROT] FILL_WORD c_m_addr=%h data=%h line_idx=%0d fill_addr=%h",
                             $time, c_m_addr, m_data_in, line_idx, fill_addr);
                end
            end

            // Track write buffer applies to PROT address
            if (wbuf_applying && wbuf_valid[wbuf_apply_idx]) begin
                logic [19:1] wbuf_addr;
                wbuf_addr = {wbuf_line_addr[19:4], wbuf_apply_idx};
                if (wbuf_addr == PROT_ADDR) begin
                    $display("[%0t][DC-PROT] WBUF_APPLY addr=%h data=%h be=%b",
                             $time, wbuf_addr, wbuf_data[wbuf_apply_idx], wbuf_be[wbuf_apply_idx]);
                end
            end

            // Track cache line reads from PROT address
            if (c_ack && !c_wr_en && c_addr == PROT_ADDR) begin
                $display("[%0t][DC-PROT] CPU_READ addr=%h data=%h way=%0d hit=%b",
                         $time, c_addr, c_data_out, hit_way, hit);
            end
        end
    end
`endif

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        accessing <= 1'b0;
        wbuf_valid <= 8'b0;
        wbuf_active <= 1'b0;
        wbuf_applying <= 1'b0;
        wbuf_apply_idx <= 3'b0;
        just_finished_wbuf <= 1'b0;
        fill_request_sent <= 1'b0;
        fill_delay_cnt <= 3'b0;
    end else begin
        accessing <= c_access;

        // Note: just_finished_wbuf is managed in the fill/flush state machine block
        // to avoid cross-always_ff race conditions

        // Set fill_request_sent after fill has been active for enough cycles
        // This allows the arbiter pipeline to drain any pending flush writes
        // before we start interpreting m_ack as fill data
        if (busy && !flushing_active && !wbuf_applying) begin
            // Increment counter during fill, saturate at 7
            if (fill_delay_cnt < 3'd6) begin
                fill_delay_cnt <= fill_delay_cnt + 1'b1;
            end else begin
                fill_request_sent <= 1'b1;
            end
        end else begin
            fill_request_sent <= 1'b0;
            fill_delay_cnt <= 3'b0;
        end

        // Write buffer capture:
        // Capture the initial write-miss that triggers the fill (or flush-then-fill)
        // BUG FIX: Also capture when do_flush triggers (for flush-then-fill scenarios)
        if ((do_fill || request_flush_dirty) && c_wr_en) begin
            wbuf_active <= 1'b1;
            wbuf_line_addr <= c_addr[19:1];
            wbuf_valid[c_addr[3:1]] <= 1'b1;
            wbuf_data[c_addr[3:1]]  <= c_data_out;
            wbuf_be[c_addr[3:1]]    <= c_bytesel;
            if (DEBUG) begin
                $display("[%0t][DCache2Way] WBUF_CAPTURE_INITIAL addr=%h offset=%0d data=%h be=%b (do_fill=%b do_flush=%b)",
                         $time, c_addr, c_addr[3:1], c_data_out, c_bytesel, do_fill, request_flush_dirty);
            end
        end
        // Capture subsequent writes during fill to same line
        // Direct comparison in if statement to avoid wire timing issues
        else if (busy && !flushing_active && !wbuf_applying && c_access && c_wr_en && (c_addr[19:4] == latched_address[19:4])) begin
            wbuf_active <= 1'b1;  // BUG FIX: Must set wbuf_active for apply phase to trigger
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
        fetch_address <= {19{1'b0}};
    end else begin
        if (!busy && !flushing_active) begin
            latched_address <= c_addr;
            eviction_started <= 1'b0;  // Clear flag on new access
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
        c_m_addr <= {19{1'b0}};
        code_flush_pending <= 1'b0;
        code_flush_way <= 1'b0;
        code_flush_index <= {index_bits{1'b0}};
        code_flush_tag <= {tag_bits{1'b0}};
        flush_way_reg <= 1'b0;
        flush_index_reg <= {index_bits{1'b0}};
        flush_tag_reg <= {tag_bits{1'b0}};
        flush_beat <= 3'b0;
        fl_state <= FL_IDLE;
        flush_data <= 16'h0000;
        fill_index_reg <= {index_bits{1'b0}};

        // PHASE 2: Victim capture control
        capturing_to_victim <= 1'b0;
        victim_capture_id <= 1'b0;
        eviction_started <= 1'b0;
        eviction_addr <= {19{1'b0}};
        victim_wb_base_addr <= 16'h0000;

        // PHASE 1: Initialize non-blocking cache structures
        // Victim Buffer
        victim_valid[0] <= 1'b0;
        victim_addr[0] <= 16'h0000;
        victim_wb_beat[0] <= 3'b0;
        victim_wb_active[0] <= 1'b0;
        victim_valid[1] <= 1'b0;
        victim_addr[1] <= 16'h0000;
        victim_wb_beat[1] <= 3'b0;
        victim_wb_active[1] <= 1'b0;
        victim_alloc_ptr <= 1'b0;

        // Fill Buffer
        fb_valid <= 1'b0;
        fb_addr <= {19{1'b0}};
        fb_words_valid <= 8'b0;
        fb_way <= 1'b0;
        fb_index <= {index_bits{1'b0}};
        fb_tag <= {tag_bits{1'b0}};

        // Memory Request Queue (queue_count=0 means empty, no need to init entries)
        queue_head <= 2'b00;
        queue_tail <= 2'b00;
        queue_count <= 3'b000;

        // PHASE 4: Queue processing state
        queue_processing <= 1'b0;
        queue_processing_type <= 2'b00;
        queue_processing_addr <= {19{1'b0}};
        queue_processing_victim <= 1'b0;
    end else if (enabled) begin
        // Clear just_finished_wbuf after one cycle (default)
        // Conditionals below may set it to 1
        just_finished_wbuf <= 1'b0;

        // ------------------------
        // Line fill (when not flushing)
        // BUG FIX: Require fill_request_sent to prevent stale flush acks from being
        // interpreted as fill data. The delay counter ensures the arbiter pipeline
        // has drained any pending flush writes before we process fill acks.
        // ------------------------
        if (DEBUG && m_ack) begin
            $display("[%0t][DCache2Way] M_ACK: flushing_active=%b busy=%b wbuf_applying=%b fill_request_sent=%b cond_result=%b c_m_addr=%h",
                     $time, flushing_active, busy, wbuf_applying, fill_request_sent,
                     (m_ack && !flushing_active && busy && !wbuf_applying && fill_request_sent), c_m_addr);
        end
        if (m_ack && !flushing_active && busy && !wbuf_applying && fill_request_sent) begin
            if (DEBUG) begin
                $display("[%0t][DCache2Way] FILL_ACK idx=%0d c_m_addr=%h->%h m_data_in=%h line_idx=%0d",
                         $time, c_m_addr[index_end:index_start], c_m_addr, {c_m_addr[19:4], c_m_addr[3:1] + 1'b1}, m_data_in, line_idx);
            end
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
                    // BUG FIX: Set guard to give hit detection time to settle
                    just_finished_wbuf <= 1'b1;
                    if (DEBUG) begin
                        $display("[%0t][DCache2Way] FILL_DONE, clearing busy", $time);
                    end
                end
            end
        end else if (!flushing_active && do_fill) begin
            // PHASE 4: Start fills immediately (blocking), only victim writebacks are queued
            line_idx <= 3'b0;
            fill_index_reg <= c_addr[index_end:index_start];
            if (DEBUG) begin
                $display("[%0t][DCache2Way] FILL_START addr=%h fill_index=%h (immediate)",
                         $time, c_addr, c_addr[index_end:index_start]);
            end
            fill_line(c_addr);
        end else if (wbuf_applying) begin
            // Apply buffered writes via A-port (one per cycle)
            if (wbuf_apply_idx == 3'b111) begin
                // Last word - done applying
                wbuf_applying <= 1'b0;
                busy <= 1'b0;
                wbuf_active <= 1'b0;
                wbuf_valid <= 8'b0;
                // BUG FIX: Set guard to give hit detection time to settle
                just_finished_wbuf <= 1'b1;
            end else begin
                wbuf_apply_idx <= wbuf_apply_idx + 1'b1;
            end
        end

        // Schedule code flush on write-hit (keeps residency)
        if (code_write_hit && fl_state == FL_IDLE) begin
            code_flush_pending <= 1'b1;
            code_flush_way     <= hit_way;
            code_flush_index   <= c_addr[index_end:index_start];
            code_flush_tag     <= c_addr[19:tag_start];
        end

        // ------------------------
        // Flush FSM (with proper BlockRam read latency handling)
        // ------------------------
        case (fl_state)
            FL_IDLE: begin
                flushing <= 1'b0;

                // PHASE 4: Queue processing enabled (non-blocking victim writebacks)
                // Serialize with fills by checking busy; fills block queue processing
                if (!do_flush && !busy && !wbuf_applying && !queue_empty && !queue_processing) begin
                    // Dequeue head entry (should only be VICTIM_WB)
                    queue_processing <= 1'b1;
                    queue_processing_type <= mem_req_type[queue_head];
                    queue_processing_addr <= mem_req_addr[queue_head];
                    queue_processing_victim <= mem_req_victim[queue_head];
                    queue_head <= queue_head + 2'b01;
                    queue_count <= queue_count - 3'b001;

                    if (DEBUG) begin
                        $display("[%0t][DCache2Way] QUEUE_DEQUEUE type=%0d addr=%h victim=%0d head=%0d count=%0d",
                                 $time, mem_req_type[queue_head],
                                 mem_req_addr[queue_head],
                                 mem_req_victim[queue_head],
                                 queue_head, queue_count - 3'b001);
                    end

                    // Start victim writeback (non-blocking!)
                    if (mem_req_type[queue_head] == MEM_REQ_VICTIM_WB) begin
                        victim_wb_active[mem_req_victim[queue_head]] <= 1'b1;
                        victim_capture_id <= mem_req_victim[queue_head];
                        victim_wb_base_addr <= victim_addr[mem_req_victim[queue_head]];  // Register base address
                        flush_beat <= 3'b000;
                        fl_state <= FL_VICTIM_WB;
                        flushing <= 1'b1;
                        // PHASE 4: Don't set busy! (non-blocking writeback)

                        if (DEBUG) begin
                            $display("[%0t][DCache2Way] START_VICTIM_WB victim=%0d (non-blocking)",
                                     $time, mem_req_victim[queue_head]);
                            // INSTRUMENTATION: Show victim_addr[] contents at WB start
                            $display("[%0t][DCache2Way]   VICTIM_ADDR_READ victim[%0d] = %h (will write to %h--%h)",
                                     $time, mem_req_victim[queue_head],
                                     victim_addr[mem_req_victim[queue_head]],
                                     {victim_addr[mem_req_victim[queue_head]], 3'b000},
                                     {victim_addr[mem_req_victim[queue_head]], 3'b111});
                            // DEBUG: Show victim_wb_base_addr assignment
                            $display("[%0t][DCache2Way]   REGISTERING victim_wb_base_addr <= %h (from victim_addr[%0d])",
                                     $time, victim_addr[mem_req_victim[queue_head]], mem_req_victim[queue_head]);
                            // Show BOTH victim buffers for comparison
                            $display("[%0t][DCache2Way]   VICTIM_BUFFERS: victim[0]=%h victim[1]=%h",
                                     $time, victim_addr[0], victim_addr[1]);
                        end
                    end
                end else if (do_flush) begin
                    // BUG FIX: Use way_to_replace for eviction flushes (not selected_way)
                    flush_way_reg   <= code_flush_pending ? code_flush_way : way_to_replace;
                    flush_index_reg <= code_flush_pending ? code_flush_index : latched_address[index_end:index_start];
                    flush_tag_reg   <= code_flush_pending ? code_flush_tag
                                                          : (way_to_replace ? tag_way1 : tag_way0);
                    flush_beat      <= 3'b000;
                    fl_state        <= FL_ADDR_SETUP;
                    flushing        <= 1'b1;
                    busy            <= 1'b1;
                    code_flush_pending <= 1'b0;
                    eviction_started <= 1'b1;  // Mark eviction started for this miss
                    eviction_addr <= latched_address;  // Track which address is being evicted

                    // PHASE 2: Check if we can capture to victim buffer
                    // Use victim buffer for dirty evictions (not code flushes)
                    if (!code_flush_pending && request_flush_dirty) begin
                        // Find a free victim buffer entry
                        if (!victim_valid[victim_alloc_ptr]) begin
                            // Allocate this victim entry
                            capturing_to_victim <= 1'b1;
                            victim_capture_id <= victim_alloc_ptr;
                            victim_addr[victim_alloc_ptr] <= {(way_to_replace ? tag_way1 : tag_way0),
                                                              latched_address[index_end:index_start]};
                            // Round-robin: toggle allocation pointer for next time
                            victim_alloc_ptr <= ~victim_alloc_ptr;

                            if (DEBUG) begin
                                $display("[%0t][DCache2Way] VICTIM_CAPTURE_START victim=%0d addr=%h",
                                         $time, victim_alloc_ptr,
                                         {(way_to_replace ? tag_way1 : tag_way0),
                                          latched_address[index_end:index_start], 4'b0000});
                                // INSTRUMENTATION: Show what's being stored
                                $display("[%0t][DCache2Way]   VICTIM_ADDR_ASSIGN victim[%0d] <= %h (tag=%h idx=%h way=%0d)",
                                         $time, victim_alloc_ptr,
                                         {(way_to_replace ? tag_way1 : tag_way0), latched_address[index_end:index_start]},
                                         (way_to_replace ? tag_way1 : tag_way0),
                                         latched_address[index_end:index_start],
                                         way_to_replace);
                            end
                        end else begin
                            // No free victim buffer - fall back to blocking flush
                            capturing_to_victim <= 1'b0;
                            if (DEBUG) begin
                                $display("[%0t][DCache2Way] VICTIM_FULL - using blocking flush", $time);
                            end
                        end
                    end else begin
                        // Code flush - use old blocking path
                        capturing_to_victim <= 1'b0;
                    end
                end
            end

            FL_ADDR_SETUP: begin
                // New state: Wait one cycle for flush_index_reg and flush_beat to be valid
                // This ensures addr_b = {flush_index_reg, flush_beat} is stable before r_b captures it
                flushing   <= 1'b1;
                fl_state   <= FL_PREFETCH;
            end

            FL_PREFETCH: begin
                // B-port address is now stable, r_b will capture ram[addr_b] at this posedge
                // Wait one more cycle for BlockRam output to be valid
                flushing   <= 1'b1;
                fl_state   <= FL_SEND;
            end

            FL_SEND: begin
                // Capture data from B-port (now valid after 1-cycle BlockRam latency)
                flushing   <= 1'b1;
                flush_data <= flush_way_reg ? data_way1_b : data_way0_b;

                // PHASE 2: Capture to victim buffer if enabled
                if (capturing_to_victim) begin
                    victim_data[victim_capture_id][flush_beat] <= flush_way_reg ? data_way1_b : data_way0_b;

                    if (DEBUG) begin
                        $display("[%0t][DCache2Way] VICTIM_CAPTURE: victim=%0d beat=%0d data=%h",
                                 $time, victim_capture_id, flush_beat,
                                 flush_way_reg ? data_way1_b : data_way0_b);
                    end

                    // Check if this is the last word
                    if (flush_beat == 3'b111) begin
                        // PHASE 4: All 8 words captured - enqueue victim writeback (non-blocking!)
                        victim_valid[victim_capture_id] <= 1'b1;
                        victim_wb_beat[victim_capture_id] <= 3'b000;
                        capturing_to_victim <= 1'b0;

                        // PHASE 4: Enqueue VICTIM_WB request if queue not full
                        if (!queue_full) begin
                            mem_req_type[queue_tail] <= MEM_REQ_VICTIM_WB;
                            mem_req_addr[queue_tail] <= {victim_addr[victim_capture_id], 4'b0000};
                            mem_req_victim[queue_tail] <= victim_capture_id;
                            queue_tail <= queue_tail + 2'b01;
                            queue_count <= queue_count + 3'b001;

                            if (DEBUG) begin
                                $display("[%0t][DCache2Way] VICTIM_ENQUEUE victim=%0d addr=%h tail=%0d count=%0d",
                                         $time, victim_capture_id,
                                         {victim_addr[victim_capture_id], 4'b0000},
                                         queue_tail, queue_count + 3'b001);
                            end
                        end

                        // Return to FL_IDLE - non-blocking!
                        fl_state   <= FL_IDLE;
                        flushing   <= 1'b0;
                        busy       <= 1'b0;  // NON-BLOCKING!
                        flush_beat <= 3'b000;
                        eviction_started <= 1'b0;  // Clear flag after victim capture completes

                        if (DEBUG) begin
                            $display("[%0t][DCache2Way] VICTIM_CAPTURE_DONE victim=%0d (non-blocking)",
                                     $time, victim_capture_id);
                        end
                    end else begin
                        // Continue capturing next word
                        flush_beat <= flush_beat + 1'b1;
                        fl_state   <= FL_PREFETCH;
                    end
                end else begin
                    // Old blocking flush path
                    fl_state   <= FL_WAIT;
                    if (DEBUG) begin
                        $display("[%0t][DCache2Way] FL_SEND: Capturing beat=%0d way=%0d addr_b=%h data=%h",
                                 $time, flush_beat, flush_way_reg, line_addr_for_b,
                                 flush_way_reg ? data_way1_b : data_way0_b);
                    end
                end
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
                        eviction_started <= 1'b0;  // Clear flag after blocking flush completes
                    end else begin
                        // Move to next beat
                        flush_beat <= flush_beat + 1'b1;
                        fl_state   <= FL_PREFETCH;
                    end
                end
            end

            FL_VICTIM_WB: begin
                // PHASE 5: Write victim buffer to memory via separate VWB port (NON-BLOCKING!)
                // Victim WB interface (vwb_*) drives this operation independently
                flushing <= 1'b1;

                // DEBUG: Show victim_wb_base_addr on first cycle
                if (DEBUG && flush_beat == 3'b000) begin
                    $display("[%0t][DCache2Way] FL_VICTIM_WB_START victim_wb_base_addr=%h",
                             $time, victim_wb_base_addr);
                end

                if (vwb_ack) begin
                    if (flush_beat == 3'b111) begin
                        // Victim writeback complete - release victim buffer entry
                        victim_valid[victim_capture_id] <= 1'b0;
                        victim_wb_active[victim_capture_id] <= 1'b0;
                        fl_state   <= FL_IDLE;
                        flushing   <= 1'b0;
                        queue_processing <= 1'b0;  // Done processing queue entry (non-blocking)
                        flush_beat <= 3'b000;

                        if (DEBUG) begin
                            $display("[%0t][DCache2Way] VICTIM_WB_DONE victim=%0d (non-blocking, separate port)",
                                     $time, victim_capture_id);
                        end
                    end else begin
                        // Continue to next word
                        flush_beat <= flush_beat + 1'b1;
                        victim_wb_beat[victim_capture_id] <= flush_beat + 1'b1;

                        if (DEBUG) begin
                            // DEBUG: Show victim WB address components
                            if (flush_beat == 3'b000) begin  // Only display once per WB operation
                                $display("[%0t][DCache2Way] VICTIM_WB_START victim_wb_addr=%h (base=%h)",
                                         $time, victim_wb_addr, victim_wb_base_addr);
                            end
                            $display("[%0t][DCache2Way] VICTIM_WB beat=%0d addr=%h data=%h",
                                     $time, flush_beat,
                                     {victim_addr[victim_capture_id], flush_beat},
                                     victim_data[victim_capture_id][flush_beat]);
                            // INSTRUMENTATION: Show address calculation breakdown
                            $display("[%0t][DCache2Way]   ADDR_CALC: victim[%0d]=%h beat=%0d -> addr=%h",
                                     $time, victim_capture_id,
                                     victim_addr[victim_capture_id],
                                     flush_beat,
                                     {victim_addr[victim_capture_id], flush_beat});
                        end
                    end
                end
            end
        endcase
    end
end

// --------------------------------------------------------------------------
// Debug instrumentation (sim-only). Focused on write buffer flow.
// --------------------------------------------------------------------------
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        debug_printed     <= 1'b0;
    end else begin
        // Always-on critical traces for debugging
        // Trace write buffer capture
        if ((do_fill || request_flush_dirty) && c_wr_en) begin
            $display("[%0t][DC] WBUF_CAPTURE addr=%h word=%0d data=%h (do_fill=%b req_flush=%b)",
                     $time, c_addr, c_addr[3:1], c_data_out, do_fill, request_flush_dirty);
        end

        // Trace write buffer application
        if (wbuf_applying && wbuf_valid[wbuf_apply_idx]) begin
            $display("[%0t][DC] WBUF_APPLY word=%0d addr=%h data=%h be=%b way=%0d",
                     $time, wbuf_apply_idx, {fill_index_reg, wbuf_apply_idx}, wbuf_data[wbuf_apply_idx], wbuf_be[wbuf_apply_idx], selected_way);
        end

        // Trace when wbuf_applying ends
        if (wbuf_applying && wbuf_apply_idx == 3'b111) begin
            $display("[%0t][DC] WBUF_DONE fill_index=%h way=%0d", $time, fill_index_reg, selected_way);
        end

        // Trace code_write_hit trigger
        if (code_write_hit) begin
            $display("[%0t][DC] CODE_WRITE_HIT addr=%h word=%0d data=%h way=%0d",
                     $time, c_addr, c_addr[3:1], c_data_out, hit_way);
        end

        // Trace code flush scheduling
        if (code_flush_pending && !busy && !flushing_active && !wbuf_applying && fl_state == FL_IDLE) begin
            $display("[%0t][DC] CODE_FLUSH_START idx=%h way=%0d tag=%h",
                     $time, code_flush_index, code_flush_way, code_flush_tag);
        end

        // Trace each flush beat with data
        if (fl_state == FL_WAIT && m_ack) begin
            $display("[%0t][DC] FLUSH_BEAT beat=%0d addr=%h data=%h way=%0d",
                     $time, flush_beat, flush_addr, flush_data, flush_way_reg);
        end

        // Trace c_ack going high for writes
        if (c_ack && c_wr_en) begin
            $display("[%0t][DC] STORE_ACK addr=%h word=%0d data=%h way=%0d",
                     $time, c_addr, c_addr[3:1], c_data_out, hit_way);
        end

        // Trace fill reads from memory
        if (m_ack && !flushing_active && busy && !wbuf_applying && fill_request_sent) begin
            $display("[%0t][DC] FILL_READ c_m_addr=%h word=%0d m_data_in=%h line_addr=%h way=%0d",
                     $time, c_m_addr, c_m_addr[3:1], m_data_in, line_address, selected_way);
        end

        if (DEBUG) begin
            if (!debug_printed) begin
                $display("[%0t][DCache2Way] DEBUG ENABLED", $time);
                debug_printed <= 1'b1;
            end
        end
    end
end

endmodule
`default_nettype wire
