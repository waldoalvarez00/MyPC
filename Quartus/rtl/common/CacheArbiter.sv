// Copyright 2025, Waldo Alvarez
// Cache Arbiter for Harvard Architecture
// Arbitrates between I-Cache and D-Cache memory requests
// Priority: D-cache > I-cache (data accesses are more critical)

`default_nettype none

module CacheArbiter(
    input logic clk,
    input logic reset,

    // I-Cache interface
    input logic [19:1] icache_m_addr,
    output logic [15:0] icache_m_data_in,
    input logic icache_m_access,
    output logic icache_m_ack,

    // D-Cache interface
    input logic [19:1] dcache_m_addr,
    output logic [15:0] dcache_m_data_in,
    input logic [15:0] dcache_m_data_out,
    input logic dcache_m_access,
    output logic dcache_m_ack,
    input logic dcache_m_wr_en,
    input logic [1:0] dcache_m_bytesel,

    // Memory interface (to SDRAM arbiter)
    output logic [19:1] mem_m_addr,
    input logic [15:0] mem_m_data_in,
    output logic [15:0] mem_m_data_out,
    output logic mem_m_access,
    input logic mem_m_ack,
    output logic mem_m_wr_en,
    output logic [1:0] mem_m_bytesel
);

// State machine for arbitration
typedef enum logic [1:0] {
    IDLE,
    SERVING_DCACHE,
    SERVING_ICACHE
} state_t;

state_t state, next_state;

// Registered selection
logic serving_dcache, serving_icache;

// State machine
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        state <= IDLE;
        serving_dcache <= 1'b0;
        serving_icache <= 1'b0;
    end else begin
        state <= next_state;

        case (next_state)
            SERVING_DCACHE: begin
                serving_dcache <= 1'b1;
                serving_icache <= 1'b0;
            end
            SERVING_ICACHE: begin
                serving_dcache <= 1'b0;
                serving_icache <= 1'b1;
            end
            default: begin
                serving_dcache <= 1'b0;
                serving_icache <= 1'b0;
            end
        endcase
    end
end

// Next state logic with priority
always_comb begin
    next_state = state;

    case (state)
        IDLE: begin
            // D-cache has priority
            if (dcache_m_access)
                next_state = SERVING_DCACHE;
            else if (icache_m_access)
                next_state = SERVING_ICACHE;
        end

        SERVING_DCACHE: begin
            // Stay serving D-cache until ack
            if (mem_m_ack)
                next_state = IDLE;
        end

        SERVING_ICACHE: begin
            // Stay serving I-cache until ack
            if (mem_m_ack)
                next_state = IDLE;
        end

        default: next_state = IDLE;
    endcase
end

// Output multiplexing
always_comb begin
    // Default values
    mem_m_addr = 19'b0;
    mem_m_data_out = 16'b0;
    mem_m_access = 1'b0;
    mem_m_wr_en = 1'b0;
    mem_m_bytesel = 2'b11;

    dcache_m_ack = 1'b0;
    icache_m_ack = 1'b0;

    if (serving_dcache) begin
        // Route D-cache to memory
        mem_m_addr = dcache_m_addr;
        mem_m_data_out = dcache_m_data_out;
        mem_m_access = dcache_m_access;
        mem_m_wr_en = dcache_m_wr_en;
        mem_m_bytesel = dcache_m_bytesel;
        dcache_m_ack = mem_m_ack;
    end else if (serving_icache) begin
        // Route I-cache to memory
        mem_m_addr = icache_m_addr;
        mem_m_access = icache_m_access;
        mem_m_wr_en = 1'b0;  // I-cache is read-only
        mem_m_bytesel = 2'b11;
        icache_m_ack = mem_m_ack;
    end
end

// Data input distribution (both caches get the same data)
assign dcache_m_data_in = mem_m_data_in;
assign icache_m_data_in = mem_m_data_in;

endmodule

`default_nettype wire
