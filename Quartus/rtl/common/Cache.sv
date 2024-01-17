// Copyright Jamie Iles, 2018
//
// This file is part of s80x86.
//
// s80x86 is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// s80x86 is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with s80x86.  If not, see <http://www.gnu.org/licenses/>.


/*

This SystemVerilog module defines a Cache hardware component. It's designed to interface between a front-end (such as a CPU) and a back-end memory system. 
Let's break it down to understand its functionality:

Module Interface
Inputs:
clk, reset, enabled: Standard control signals for clock, reset, and enable.
Frontend interface (c_ prefix): Connects to the CPU or similar device. Includes address (c_addr), data in (c_data_in), data out (c_data_out), access (c_access), acknowledge (c_ack), write enable (c_wr_en), and byte select (c_bytesel) signals.
Backend interface (m_ prefix): Connects to the memory system. Similar signals to the frontend interface but for interacting with the main memory.

Cache Parameters
Cache Size: Defined by the lines parameter, indicating the number of cache lines.
Line Size: Each cache line size is set by line_size.
Index and Tag Bits: Used for addressing within the cache. The tag bits are derived from the address bits, subtracting the bits used for indexing and offset within a line.

Internal Registers and Logic
Tag, Valid, and Dirty Flags: The cache maintains tag arrays, valid bits, and dirty bits for each line to manage cache coherency and state.
Dual-Port RAM (DPRam) Instances: Used for storing tags, valid, and dirty bits.
Block RAM (BlockRam) Instance: Used for storing the actual data of the cache lines.
Flush and Fill Logic: Handles scenarios where cache lines are replaced, either by writing back modified data to memory (flush_line) or bringing new data into the cache (fill_line).

Cache Operation
Hit and Miss Determination:
The cache checks if the requested data is present (hit) or not (miss).

Data Fetch or Write-Back:
On a miss, the cache either fetches data from the main memory or writes back dirty data.

Data Access:
On a hit, the cache provides data directly to the frontend.

Special Considerations
No Reset Logic for Cache State: Notably, the cache state is preserved across resets, as indicated by the comment. 
This is unusual and specific to the system's requirements, where the CPU is not cache-coherent.

Write Policies: The cache handles writes and updates its state accordingly, including setting the dirty bit.

State Machine: Controlled by the clock, the cache logic updates its state based on various conditions like access requests, flush/fill operations, and memory acknowledgments.
Overall Function

The Cache module serves as an intermediary to speed up data access between a slower memory system and a faster CPU or processor. It utilizes 
common caching strategies like tag comparison, dirty bit management, and valid bit checking to ensure efficient and coherent data access 
and storage. The module is quite complex, indicating it's designed for a specific system with unique requirements, 
especially given the custom flush and fill logic and the decision to preserve cache state across resets.




The module implements a cache, but to precisely determine the type of cache it is (like direct-mapped, set-associative, or fully associative), 
we need to analyze certain key aspects of the design:

Tag, Index, and Offset Calculation:

The cache uses tag_bits, index_bits, and an offset to address the cache lines. This suggests a structure where each
line is uniquely identified by its index, and within each line, a tag is used to verify if the requested data is 
actually stored in that line.

Indexing Scheme:

The cache appears to use a portion of the address (c_addr[index_end:index_start]) to determine the index of a cache line. 
This is a typical feature of direct-mapped or set-associative caches.

Tag Comparison:

The cache compares the tag portion of the address with the stored tag (tags_match = tag == fetch_address[19:tag_start]) to check for a hit.

Direct-Mapped vs. Set-Associative:

In a direct-mapped cache, each memory location maps to exactly one line in the cache. This is typically implemented with a straightforward index-to-line mapping.

In a set-associative cache, each memory location can map to any one of a set of lines. This requires additional logic to determine which line within the set to use.

Fully Associative:

A fully associative cache does not use an index; any memory location can be cached in any line, with the decision based solely on tags and replacement policies.

Based on the provided code, it's most likely a direct-mapped or set-associative cache. The exact type (direct-mapped vs. set-associative) 
depends on how the index is used to address multiple cache lines. If each index corresponds to exactly one cache line, it's direct-mapped. 

If each index can address a set of lines (and the code includes logic to choose among these lines), it's set-associative.

The module does not seem to be fully associative, as there is a clear use of indices to address cache lines. The specific 
type (direct-mapped or set-associative) would be clearer if the policy for selecting among potentially multiple lines 
per index (in the case of set-associative) was specified.

*/


//verilator lint_off UNUSED
`default_nettype none
module Cache(input logic clk,
             input logic reset,
             input logic enabled,
			 
             // Frontend
             input logic [19:1] c_addr,        // 512 K * 2bytes
             output logic [15:0] c_data_in,    // 2 bytes
             input logic [15:0] c_data_out,
             input logic c_access,
             output logic c_ack,
             input logic c_wr_en,
             input logic [1:0] c_bytesel,
			 
             // Backend
             output logic [19:1] m_addr,
             input logic [15:0] m_data_in,
             output logic [15:0] m_data_out,
             output logic m_access,
             input logic m_ack,
             output logic m_wr_en,
             output logic [1:0] m_bytesel);

parameter lines = 512;

localparam line_size = 8;
localparam index_bits = $clog2(lines);
localparam tag_bits = 19 - 3 - index_bits;
localparam index_start = 4;
localparam index_end = 4 + index_bits - 1;
localparam tag_start = 4 + index_bits;

reg [19:1] c_m_addr;
reg [15:0] c_m_data_out;
reg [2:0] line_idx;
wire [19:tag_start] tag;
reg [7:0] line_valid;
reg busy;
reg flushing;
wire dirty;
wire write_line = m_ack && !flushing;
reg [index_end-1:0] line_address;
reg [19:1] latched_address, fetch_address;
reg updating;
reg accessing;
wire tags_match = tag == fetch_address[19:tag_start];
wire filling_current = fetch_address[19:index_start] == latched_address[19:index_start];
wire hit = accessing && ((valid && tags_match) ||
    (busy && filling_current && line_valid[fetch_address[3:1]]));

wire [15:0] c_q;
assign c_data_in = enabled ? (c_ack ? c_q : 16'b0) : m_data_in;
assign c_ack = enabled ? accessing & !flushing & hit : m_ack;

assign m_addr = enabled ? c_m_addr : c_addr;
assign m_wr_en = enabled ? flushing & ~m_ack : c_wr_en;
assign m_access = enabled ? busy & ~m_ack : c_access;
assign m_bytesel = enabled ? 2'b11 : c_bytesel;
assign m_data_out = enabled ? c_m_data_out : c_data_out;

wire do_flush = updating && ~hit && !busy && !flushing && dirty;
wire do_fill = updating && ~hit && !busy && !flushing && !dirty;

wire write_tag = do_fill;
wire valid;
wire write_valid = do_flush | write_tag | (~flushing && line_idx == 3'b111 && m_ack);

DPRam #(.words(lines),
        .width(tag_bits))
      TagRam(.clk(clk),
             .addr_a(c_addr[index_end:index_start]),
             .wr_en_a(1'b0),
             .wdata_a({tag_bits{1'b0}}),
             .q_a(tag),
             .addr_b(latched_address[index_end:index_start]),
             .wr_en_b(write_tag),
             .wdata_b(latched_address[19:tag_start]),
             // verilator lint_off PINCONNECTEMPTY
             .q_b());
             // verilator lint_on PINCONNECTEMPTY

DPRam #(.words(lines),
        .width(1))
      ValidRam(.clk(clk),
               .addr_a(c_addr[index_end:index_start]),
               .wr_en_a(1'b0),
               .wdata_a(1'b0),
               .q_a(valid),
               .addr_b(latched_address[index_end:index_start]),
               .wr_en_b(write_valid),
               .wdata_b(do_flush ? 1'b0 : (~flushing && line_idx == 3'b111)),
               // verilator lint_off PINCONNECTEMPTY
               .q_b());
               // verilator lint_on PINCONNECTEMPTY

DPRam #(.words(lines),
        .width(1))
      DirtyRam(.clk(clk),
               .addr_a(c_addr[index_end:index_start]),
               .wr_en_a(c_ack & c_wr_en),
               .wdata_a(1'b1),
               // verilator lint_off PINCONNECTEMPTY
               .q_a(dirty),
               // verilator lint_on PINCONNECTEMPTY
               .addr_b(latched_address[index_end:index_start]),
               .wr_en_b(do_flush),
               .wdata_b(1'b0),
               // verilator lint_off PINCONNECTEMPTY
               .q_b());
               // verilator lint_on PINCONNECTEMPTY

BlockRam #(.words(lines * line_size))
         LineRAM(.clk(clk),
                 .addr_a(c_addr[index_end:1]),
                 .wr_en_a(c_ack && c_wr_en && !flushing && hit),
                 .wdata_a(c_data_out),
                 .be_a(c_bytesel),
                 .q_a(c_q),
                 .addr_b(line_address),
                 .wr_en_b(write_line),
                 .wdata_b(m_data_in),
                 .q_b(c_m_data_out),
                 .be_b(2'b11));

task flush_line;
begin
    c_m_addr <= {tag, latched_address[index_end:index_start], 3'b0};
    busy <= 1'b1;
    flushing <= 1'b1;
end
endtask

task fill_line;
begin
    c_m_addr <= c_addr;
    busy <= 1'b1;
    line_valid <= 8'b0;
end
endtask

// No reset: the CPU isn't cache coherent so we need to preserve state across
// reset
always_ff @(posedge reset)
    ;

always_ff @(posedge clk)
    accessing <= c_access;

always_comb begin
    if (m_ack && flushing)
        line_address = {latched_address[index_end:index_start], c_m_addr[3:1] + 1'b1};
    else if (~hit && !flushing && !busy && dirty)
        line_address = {latched_address[index_end:index_start], 3'b0};
    else
        line_address = {latched_address[index_end:index_start], c_m_addr[3:1]};
end

always_ff @(posedge clk) begin
    if (!busy && !flushing)
        latched_address <= c_addr;
    fetch_address <= c_addr;
end

always_ff @(posedge clk) begin
    if (enabled && !busy && !flushing && c_access)
        updating <= 1'b1;
    if (updating && !(do_flush || flushing))
        updating <= 1'b0;
end

always_ff @(posedge clk) begin
    if (enabled && m_ack) begin
        c_m_addr <= {c_m_addr[19:4], c_m_addr[3:1] + 1'b1};
        line_idx <= line_idx + 1'b1;
        if (!flushing)
            line_valid[c_m_addr[3:1]] <= 1'b1;
        if (line_idx == 3'b111) begin
            busy <= 1'b0;
            if (flushing)
                flushing <= 1'b0;
        end
    end else if (enabled && do_flush)
        flush_line();
    else if (enabled && do_fill)
        fill_line();
end

endmodule
