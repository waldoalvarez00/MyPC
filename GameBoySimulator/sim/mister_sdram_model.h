// Generic MiSTer SDRAM/DDR3 Model for Verilator Simulation
// Supports both native SDRAM interface and Avalon-MM interface

#ifndef MISTER_SDRAM_MODEL_H
#define MISTER_SDRAM_MODEL_H

#include <cstdint>
#include <cstring>
#include <vector>
#include <queue>
#include <cstdio>

// Interface types
enum SDRAMInterfaceType {
    INTERFACE_NATIVE_SDRAM,   // Native 16-bit SDRAM (SDRAMController.sv style)
    INTERFACE_AVALON_64,      // Avalon-MM 64-bit (HPS ram1/ram2)
    INTERFACE_AVALON_128      // Avalon-MM 128-bit (HPS vbuf)
};

// SDRAM commands (active low encoding)
enum SDRAMCommand {
    CMD_NOP        = 0b0111,
    CMD_BST        = 0b0110,
    CMD_READ       = 0b0101,
    CMD_WRITE      = 0b0100,
    CMD_ACT        = 0b0011,
    CMD_PRE        = 0b0010,
    CMD_REF        = 0b0001,
    CMD_MRS        = 0b0000
};

// Pending burst read for Avalon interface
struct PendingRead {
    uint32_t address;
    uint8_t count;
    uint8_t remaining;
};

class MisterSDRAMModel {
public:
    // Configuration
    SDRAMInterfaceType interface_type;
    uint32_t size_bytes;
    uint32_t cas_latency;
    uint32_t burst_length;
    bool debug;

    // Memory storage
    std::vector<uint8_t> memory;

    // Statistics
    uint64_t read_count;
    uint64_t write_count;
    uint64_t refresh_count;
    uint64_t row_hits;
    uint64_t row_misses;

    // Native SDRAM state
    int current_state;
    uint16_t open_row[4];
    bool row_is_open[4];
    int pending_cycles;
    uint16_t last_read_data;
    bool read_valid;
    bool write_complete;
    bool config_done;

    // Avalon state
    std::queue<PendingRead> pending_reads;
    bool waitrequest;
    int read_latency_counter;
    std::vector<uint8_t> burst_data;
    int burst_offset;

	    MisterSDRAMModel(uint32_t size_mb = 32, SDRAMInterfaceType type = INTERFACE_NATIVE_SDRAM) {
	        interface_type = type;
	        size_bytes = size_mb * 1024 * 1024;
	        // Default to a realistic CAS latency. The controller (rtl/sdram_sim.sv)
	        // issues MRS during init which can override this per-design.
	        cas_latency = 2;
	        burst_length = 1;
	        debug = false;

        memory.resize(size_bytes, 0);

        reset();
    }

    void reset() {
        read_count = 0;
        write_count = 0;
        refresh_count = 0;
        row_hits = 0;
        row_misses = 0;

        current_state = 0;
        for (int i = 0; i < 4; i++) {
            open_row[i] = 0;
            row_is_open[i] = false;
        }
        pending_cycles = 0;
        last_read_data = 0;
        read_valid = false;
        write_complete = false;
        config_done = false;

        while (!pending_reads.empty()) pending_reads.pop();
        waitrequest = false;
        read_latency_counter = 0;
        burst_data.clear();
        burst_offset = 0;

        if (debug) printf("SDRAM: Reset complete\n");
    }

    // Native SDRAM interface - process command signals
    void processNativeSDRAM(
        bool cs_n, bool ras_n, bool cas_n, bool we_n,
        uint8_t bank, uint16_t addr,
        uint16_t wdata, uint8_t bytesel,
        uint16_t& rdata, bool& compl_out, bool& config_done_out
    ) {
        uint8_t cmd = (cs_n << 3) | (ras_n << 2) | (cas_n << 1) | we_n;

        // Clear one-cycle signals
        read_valid = false;
        write_complete = false;
        // DON'T clear rdata - let it hold until next read!
        // rdata = 0;

        // Handle pending operations
        if (pending_cycles > 0) {
            pending_cycles--;
            if (pending_cycles == 0 && current_state == 1) {
                // Read complete
                read_valid = true;
                rdata = last_read_data;
                read_count++;
                if (debug) printf("SDRAM: Read data ready, rdata=0x%04X\n", rdata);
            } else if (pending_cycles == 0 && current_state == 2) {
                // Write complete
                write_complete = true;
                write_count++;
            }
        }

        // Process new command
        switch (cmd) {
            case CMD_NOP:
                break;

            case CMD_ACT: {
                // Row activate
                if (row_is_open[bank] && open_row[bank] != addr) {
                    row_misses++;
                } else if (row_is_open[bank]) {
                    row_hits++;
                }
                open_row[bank] = addr;
                row_is_open[bank] = true;
                if (debug) printf("SDRAM: ACT bank=%d row=%d\n", bank, addr);
                break;
            }

            case CMD_READ: {
                // Read with auto-precharge if A10 set
                uint32_t row = open_row[bank];
                uint32_t col = addr & 0x3FF;  // 10-bit column for GameBoy SDRAM
                uint32_t byte_addr = calculateAddress(bank, row, col);

                // Track row hit when row is already open
                if (row_is_open[bank]) {
                    row_hits++;
                }

                if (byte_addr + 1 < size_bytes) {
                    last_read_data = memory[byte_addr] | (memory[byte_addr + 1] << 8);
                } else {
                    last_read_data = 0xDEAD;
                }

                pending_cycles = cas_latency;
                current_state = 1;

                // CRITICAL FIX: If cas_latency is 0, update rdata immediately!
                if (cas_latency == 0) {
                    rdata = last_read_data;
                    read_valid = true;
                    read_count++;
                }

                if (addr & 0x400) {
                    row_is_open[bank] = false;  // Auto-precharge
                }

                if (debug) printf("SDRAM: READ bank=%d addr=0x%06X data=0x%04X\n",
                    bank, byte_addr, last_read_data);
                break;
            }

            case CMD_WRITE: {
                // Write with auto-precharge if A10 set
                uint32_t row = open_row[bank];
                uint32_t col = addr & 0x3FF;  // 10-bit column for GameBoy SDRAM
                uint32_t byte_addr = calculateAddress(bank, row, col);

                // Track row hit when row is already open
                if (row_is_open[bank]) {
                    row_hits++;
                }

                if (byte_addr + 1 < size_bytes) {
                    // bytesel is inverted (0 = write byte)
                    if (!(bytesel & 0x01)) {
                        memory[byte_addr] = wdata & 0xFF;
                    }
                    if (!(bytesel & 0x02)) {
                        memory[byte_addr + 1] = (wdata >> 8) & 0xFF;
                    }
                }

                pending_cycles = 2;  // tRP
                current_state = 2;

                if (addr & 0x400) {
                    row_is_open[bank] = false;
                }

                if (debug) printf("SDRAM: WRITE bank=%d addr=0x%06X data=0x%04X sel=0x%02X\n",
                    bank, byte_addr, wdata, bytesel);
                break;
            }

            case CMD_PRE: {
                // Precharge
                if (addr & 0x400) {
                    // Precharge all
                    for (int i = 0; i < 4; i++) row_is_open[i] = false;
                } else {
                    row_is_open[bank] = false;
                }
                if (debug) printf("SDRAM: PRE bank=%d all=%d\n", bank, (addr >> 10) & 1);
                break;
            }

            case CMD_REF:
                refresh_count++;
                for (int i = 0; i < 4; i++) row_is_open[i] = false;
                config_done = true;  // Config done after first refresh
                if (debug) printf("SDRAM: REF\n");
                break;

            case CMD_MRS:
                // Mode register set - extract CAS latency and burst length
                cas_latency = (addr >> 4) & 0x07;
                burst_length = 1 << (addr & 0x07);
                if (burst_length > 8) burst_length = 8;
                if (debug) printf("SDRAM: MRS CAS=%d burst=%d\n", cas_latency, burst_length);
                break;

            default:
                break;
        }

        compl_out = read_valid || write_complete;
        config_done_out = config_done;
    }

    // Avalon-MM interface - process bus signals
    void processAvalon(
        bool read, bool write,
        uint32_t address, uint8_t burstcount,
        const uint8_t* writedata, uint8_t byteenable_mask,
        uint8_t* readdata, bool& readdatavalid, bool& waitrequest_out
    ) {
        readdatavalid = false;

        int data_width = (interface_type == INTERFACE_AVALON_128) ? 16 : 8;  // bytes

        // Handle write request
        if (write && !waitrequest) {
            uint32_t byte_addr = address * data_width;

            for (int i = 0; i < data_width; i++) {
                if ((byteenable_mask >> i) & 1) {
                    if (byte_addr + i < size_bytes) {
                        memory[byte_addr + i] = writedata[i];
                    }
                }
            }
            write_count++;

            if (debug) printf("SDRAM: Avalon WRITE addr=0x%08X count=%d\n", byte_addr, burstcount);
        }

        // Handle read request
        if (read && !waitrequest) {
            PendingRead pr;
            pr.address = address * data_width;
            pr.count = burstcount;
            pr.remaining = burstcount;
            pending_reads.push(pr);

            if (debug) printf("SDRAM: Avalon READ addr=0x%08X count=%d\n", pr.address, burstcount);
        }

        // Process pending reads with latency
        if (!pending_reads.empty()) {
            read_latency_counter++;

            if (read_latency_counter >= (int)cas_latency) {
                PendingRead& pr = pending_reads.front();

                // Output data
                uint32_t byte_addr = pr.address + (pr.count - pr.remaining) * data_width;
                for (int i = 0; i < data_width; i++) {
                    if (byte_addr + i < size_bytes) {
                        readdata[i] = memory[byte_addr + i];
                    } else {
                        readdata[i] = 0;
                    }
                }

                readdatavalid = true;
                read_count++;
                pr.remaining--;

                if (pr.remaining == 0) {
                    pending_reads.pop();
                    read_latency_counter = 0;
                }
            }
        }

        // Simple waitrequest - assert briefly on new transactions
        waitrequest_out = (read || write) && !waitrequest;
        waitrequest = waitrequest_out;
    }

    // Calculate byte address from bank/row/column
    // For GameBoy simulation: reconstruct linear byte address from SDRAM row/col
    // The gameboy uses: sdram_addr = mbc_addr >> 1 (word addressing)
    // Controller extracts: row = sdram_addr[22:10], col = sdram_addr[9:0], bank = sdram_addr[23:22]
    // We need to reverse this: sdram_addr = (bank << 22) | (row << 10) | col
    // Then byte_addr = sdram_addr << 1
    uint32_t calculateAddress(uint8_t bank, uint16_t row, uint16_t col) {
        // Reconstruct the word address from bank/row/col
        uint32_t sdram_addr = ((uint32_t)(bank & 0x3) << 22) | ((uint32_t)(row & 0x1FFF) << 10) | (col & 0x3FF);
        // Convert to byte address (multiply by 2)
        return sdram_addr << 1;
    }

    // Direct memory access for initialization/verification
    void write8(uint32_t addr, uint8_t data) {
        if (addr < size_bytes) memory[addr] = data;
    }

    void write16(uint32_t addr, uint16_t data) {
        if (addr + 1 < size_bytes) {
            memory[addr] = data & 0xFF;
            memory[addr + 1] = (data >> 8) & 0xFF;
        }
    }

    void write32(uint32_t addr, uint32_t data) {
        if (addr + 3 < size_bytes) {
            memory[addr] = data & 0xFF;
            memory[addr + 1] = (data >> 8) & 0xFF;
            memory[addr + 2] = (data >> 16) & 0xFF;
            memory[addr + 3] = (data >> 24) & 0xFF;
        }
    }

    uint8_t read8(uint32_t addr) {
        return (addr < size_bytes) ? memory[addr] : 0;
    }

    uint16_t read16(uint32_t addr) {
        if (addr + 1 < size_bytes) {
            return memory[addr] | (memory[addr + 1] << 8);
        }
        return 0;
    }

    uint32_t read32(uint32_t addr) {
        if (addr + 3 < size_bytes) {
            return memory[addr] | (memory[addr + 1] << 8) |
                   (memory[addr + 2] << 16) | (memory[addr + 3] << 24);
        }
        return 0;
    }

    // Fill memory region with pattern
    void fill(uint32_t start, uint32_t length, uint8_t pattern) {
        if (start + length <= size_bytes) {
            memset(&memory[start], pattern, length);
        }
    }

    // Load binary data into memory
    void loadBinary(uint32_t addr, const uint8_t* data, uint32_t length) {
        if (addr + length <= size_bytes) {
            memcpy(&memory[addr], data, length);
        }
    }

    void printStats() {
        printf("SDRAM Statistics:\n");
        printf("  Size:         %u MB\n", size_bytes / (1024 * 1024));
        printf("  Reads:        %lu\n", (unsigned long)read_count);
        printf("  Writes:       %lu\n", (unsigned long)write_count);
        printf("  Refreshes:    %lu\n", (unsigned long)refresh_count);
        printf("  Row hits:     %lu\n", (unsigned long)row_hits);
        printf("  Row misses:   %lu\n", (unsigned long)row_misses);
        if (row_hits + row_misses > 0) {
            printf("  Hit rate:     %.1f%%\n",
                100.0 * row_hits / (row_hits + row_misses));
        }
    }
};

#endif // MISTER_SDRAM_MODEL_H
