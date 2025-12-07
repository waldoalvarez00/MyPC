// DDR3 Memory Model for Verilator Simulation
// Simulates the MiSTer DDR3 (DDRAM) interface with configurable latency
//
// Based on the DE10-Nano's DDR3 memory interface used by MiSTer cores.
// The DDR3 on MiSTer has higher latency than SDRAM but larger capacity (1GB).
//
// Interface signals:
// - DDRAM_CLK: Clock
// - DDRAM_BUSY: Memory busy (stall requests)
// - DDRAM_BURSTCNT[7:0]: Burst count
// - DDRAM_ADDR[28:0]: Byte address
// - DDRAM_DOUT[63:0]: Data output (to core)
// - DDRAM_DOUT_READY: Data ready strobe
// - DDRAM_RD: Read request
// - DDRAM_DIN[63:0]: Data input (from core)
// - DDRAM_BE[7:0]: Byte enables
// - DDRAM_WE: Write enable

#ifndef DDR3_MODEL_CPP_H
#define DDR3_MODEL_CPP_H

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>
#include <queue>

class DDR3ModelCpp {
public:
    // Memory size: 1GB (MiSTer DE10-Nano DDR3)
    static const uint32_t MEM_SIZE = 1024 * 1024 * 1024;

    // Default latencies (in clock cycles)
    static const int DEFAULT_READ_LATENCY = 8;   // Higher than SDRAM
    static const int DEFAULT_WRITE_LATENCY = 4;
    static const int DEFAULT_BURST_LATENCY = 2;  // Between burst words

private:
    // Memory array (use vector for large allocation)
    std::vector<uint8_t> memory;

    // Latency configuration
    int read_latency;
    int write_latency;
    int burst_latency;

    // State machine
    enum State {
        IDLE,
        READ_WAIT,
        READ_BURST,
        WRITE
    };

    State state;
    int latency_counter;

    // Current operation
    uint32_t current_addr;
    uint8_t burst_count;
    uint8_t burst_remaining;

    // Read data queue for burst
    std::queue<uint64_t> read_queue;

    // Output signals
    uint64_t dout;
    bool dout_ready;
    bool busy;

    // Statistics
    uint64_t read_count;
    uint64_t write_count;
    uint64_t total_bytes_read;
    uint64_t total_bytes_written;

    // Debug
    bool debug_enabled;

public:
    DDR3ModelCpp(bool debug = false)
        : debug_enabled(debug) {
        memory.resize(MEM_SIZE, 0xFF);
        read_latency = DEFAULT_READ_LATENCY;
        write_latency = DEFAULT_WRITE_LATENCY;
        burst_latency = DEFAULT_BURST_LATENCY;
        reset();
    }

    void reset() {
        state = IDLE;
        latency_counter = 0;
        current_addr = 0;
        burst_count = 0;
        burst_remaining = 0;
        dout = 0;
        dout_ready = false;
        busy = false;

        // Clear read queue
        while (!read_queue.empty()) {
            read_queue.pop();
        }

        // Reset statistics
        read_count = 0;
        write_count = 0;
        total_bytes_read = 0;
        total_bytes_written = 0;
    }

    // Configure latencies
    void setLatencies(int read_lat, int write_lat, int burst_lat) {
        read_latency = read_lat;
        write_latency = write_lat;
        burst_latency = burst_lat;
    }

    // Main tick function - call every clock cycle
    // Returns DDRAM_DOUT value
    uint64_t tick(
        bool rd,              // DDRAM_RD
        bool we,              // DDRAM_WE
        uint32_t addr,        // DDRAM_ADDR[28:0]
        uint64_t din,         // DDRAM_DIN[63:0]
        uint8_t be,           // DDRAM_BE[7:0]
        uint8_t burstcnt      // DDRAM_BURSTCNT[7:0]
    ) {
        // Clear one-cycle signals
        dout_ready = false;

        // DDRAM_BUSY indicates we can't accept a new request right now
        // In MiSTer, this is for arbitration - not during normal processing
        // For simulation, keep it low unless we're in mid-burst
        // The controller can issue requests even while we're processing
        busy = false;

        switch (state) {
            case IDLE:
                // Check for new operations
                if (we) {
                    // Write operation - process immediately
                    handleWrite(addr, din, be);
                    write_count++;
                    // No latency - stay in IDLE to catch next write
                    // The DDR3 interface can accept writes every cycle

                    if (debug_enabled) {
                        printf("DDR3: Write to 0x%08X, data=0x%016llX, be=0x%02X\n",
                               addr, (unsigned long long)din, be);
                    }
                }
                else if (rd) {
                    // Read operation
                    current_addr = addr;
                    burst_count = burstcnt;
                    burst_remaining = burstcnt;
                    state = READ_WAIT;
                    latency_counter = read_latency;

                    // Prefetch all burst data
                    prefetchBurst();

                    if (debug_enabled) {
                        printf("DDR3: Read from 0x%08X, burst=%d\n", addr, burstcnt);
                    }
                }
                break;

            case READ_WAIT:
                // Wait for initial read latency
                if (latency_counter > 0) {
                    latency_counter--;
                } else {
                    // First data ready
                    if (!read_queue.empty()) {
                        dout = read_queue.front();
                        read_queue.pop();
                        dout_ready = true;
                        burst_remaining--;
                        read_count++;
                        total_bytes_read += 8;

                        if (debug_enabled) {
                            printf("DDR3: Read data=0x%016llX, remaining=%d\n",
                                   (unsigned long long)dout, burst_remaining);
                        }

                        if (burst_remaining > 0) {
                            state = READ_BURST;
                            latency_counter = burst_latency;
                        } else {
                            state = IDLE;
                        }
                    } else {
                        state = IDLE;
                    }
                }
                break;

            case READ_BURST:
                // Deliver burst data
                if (latency_counter > 0) {
                    latency_counter--;
                } else {
                    if (!read_queue.empty()) {
                        dout = read_queue.front();
                        read_queue.pop();
                        dout_ready = true;
                        burst_remaining--;
                        read_count++;
                        total_bytes_read += 8;

                        if (debug_enabled) {
                            printf("DDR3: Burst data=0x%016llX, remaining=%d\n",
                                   (unsigned long long)dout, burst_remaining);
                        }

                        if (burst_remaining > 0) {
                            latency_counter = burst_latency;
                        } else {
                            state = IDLE;
                        }
                    } else {
                        state = IDLE;
                    }
                }
                break;

            case WRITE:
                // Wait for write completion
                if (latency_counter > 0) {
                    latency_counter--;
                } else {
                    state = IDLE;
                }
                break;
        }

        return dout;
    }

    // Get output signals
    bool isDataReady() const { return dout_ready; }
    bool isBusy() const { return busy; }
    uint64_t getDataOut() const { return dout; }

    // Direct memory access (for testing/initialization)
    void pokeByte(uint32_t addr, uint8_t data) {
        if (addr < MEM_SIZE) {
            memory[addr] = data;
        }
    }

    uint8_t peekByte(uint32_t addr) const {
        if (addr < MEM_SIZE) {
            return memory[addr];
        }
        return 0xFF;
    }

    void pokeWord(uint32_t addr, uint16_t data) {
        if (addr + 1 < MEM_SIZE) {
            memory[addr] = data & 0xFF;
            memory[addr + 1] = (data >> 8) & 0xFF;
        }
    }

    uint16_t peekWord(uint32_t addr) const {
        if (addr + 1 < MEM_SIZE) {
            return memory[addr] | ((uint16_t)memory[addr + 1] << 8);
        }
        return 0xFFFF;
    }

    void pokeDWord(uint32_t addr, uint32_t data) {
        if (addr + 3 < MEM_SIZE) {
            memory[addr] = data & 0xFF;
            memory[addr + 1] = (data >> 8) & 0xFF;
            memory[addr + 2] = (data >> 16) & 0xFF;
            memory[addr + 3] = (data >> 24) & 0xFF;
        }
    }

    uint32_t peekDWord(uint32_t addr) const {
        if (addr + 3 < MEM_SIZE) {
            return memory[addr] |
                   ((uint32_t)memory[addr + 1] << 8) |
                   ((uint32_t)memory[addr + 2] << 16) |
                   ((uint32_t)memory[addr + 3] << 24);
        }
        return 0xFFFFFFFF;
    }

    void pokeQWord(uint32_t addr, uint64_t data) {
        if (addr + 7 < MEM_SIZE) {
            for (int i = 0; i < 8; i++) {
                memory[addr + i] = (data >> (i * 8)) & 0xFF;
            }
        }
    }

    uint64_t peekQWord(uint32_t addr) const {
        if (addr + 7 < MEM_SIZE) {
            uint64_t result = 0;
            for (int i = 0; i < 8; i++) {
                result |= (uint64_t)memory[addr + i] << (i * 8);
            }
            return result;
        }
        return 0xFFFFFFFFFFFFFFFFULL;
    }

    // Clear memory
    void clear(uint8_t value = 0xFF) {
        std::fill(memory.begin(), memory.end(), value);
    }

    // Load data from buffer
    void loadFromBuffer(const uint8_t* data, uint32_t size, uint32_t offset = 0) {
        if (offset + size <= MEM_SIZE) {
            memcpy(&memory[offset], data, size);
            if (debug_enabled) {
                printf("DDR3: Loaded %u bytes at offset 0x%08X\n", size, offset);
            }
        }
    }

    // Get statistics
    uint64_t getReadCount() const { return read_count; }
    uint64_t getWriteCount() const { return write_count; }
    uint64_t getTotalBytesRead() const { return total_bytes_read; }
    uint64_t getTotalBytesWritten() const { return total_bytes_written; }

    void printStats() const {
        printf("DDR3 Statistics:\n");
        printf("  Reads:  %llu (%llu bytes)\n",
               (unsigned long long)read_count,
               (unsigned long long)total_bytes_read);
        printf("  Writes: %llu (%llu bytes)\n",
               (unsigned long long)write_count,
               (unsigned long long)total_bytes_written);
    }

private:
    // Convert DDRAM_ADDR to byte address
    // DDRAM_ADDR = {4'b0011, ram_address} where ram_address = rdaddr[27:3]
    // So DDRAM_ADDR[24:0] = rdaddr[27:3] = byte_address >> 3
    // We need to multiply by 8 to get byte address
    uint32_t addrToByteAddr(uint32_t addr) const {
        // Strip the 0x30000000 prefix (bits [28:25])
        uint32_t ram_address = addr & 0x01FFFFFF;  // Keep only lower 25 bits
        // Convert cache line address to byte address (multiply by 8)
        return ram_address << 3;
    }

    void handleWrite(uint32_t addr, uint64_t data, uint8_t be) {
        // Convert to byte address (already 8-byte aligned from controller)
        uint32_t byte_addr = addrToByteAddr(addr);

        // Write bytes according to byte enables
        for (int i = 0; i < 8; i++) {
            if (be & (1 << i)) {
                uint32_t mem_addr = byte_addr + i;
                if (mem_addr < MEM_SIZE) {
                    memory[mem_addr] = (data >> (i * 8)) & 0xFF;
                    total_bytes_written++;
                }
            }
        }
    }

    void prefetchBurst() {
        // Clear any existing data
        while (!read_queue.empty()) {
            read_queue.pop();
        }

        // Convert to byte address (already 8-byte aligned)
        uint32_t addr = addrToByteAddr(current_addr);

        for (int i = 0; i < burst_count; i++) {
            uint64_t data = 0;
            uint32_t burst_addr = addr + (i * 8);

            if (burst_addr + 7 < MEM_SIZE) {
                for (int j = 0; j < 8; j++) {
                    data |= (uint64_t)memory[burst_addr + j] << (j * 8);
                }
            } else {
                data = 0xFFFFFFFFFFFFFFFFULL;
            }

            read_queue.push(data);
        }
    }
};

#endif // DDR3_MODEL_CPP_H
