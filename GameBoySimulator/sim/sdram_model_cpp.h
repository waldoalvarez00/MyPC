// C++ SDRAM Model for Verilator Simulation
// Models ISSI IS42S16320B/F - 512Mbit (64MB) SDRAM
//
// This C++ model provides:
// - Cycle-accurate SDRAM behavior
// - Direct integration with Verilator testbench
// - Better performance than Verilog behavioral model
// - Easy memory inspection and file loading

#ifndef SDRAM_MODEL_CPP_H
#define SDRAM_MODEL_CPP_H

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>

class SDRAMModelCpp {
public:
    // Configuration
    static const int SIZE_MB = 64;
    static const int SIZE_BYTES = SIZE_MB * 1024 * 1024;
    static const int SIZE_WORDS = SIZE_BYTES / 2;
    static const int NUM_BANKS = 4;
    static const int NUM_ROWS = 8192;
    static const int NUM_COLS = 1024;

    // CAS latency options
    static const int CAS_LATENCY_2 = 2;
    static const int CAS_LATENCY_3 = 3;

    // SDRAM Commands (active low encoding)
    static const uint8_t CMD_NOP        = 0b0111;
    static const uint8_t CMD_ACTIVE     = 0b0011;
    static const uint8_t CMD_READ       = 0b0101;
    static const uint8_t CMD_WRITE      = 0b0100;
    static const uint8_t CMD_PRECHARGE  = 0b0010;
    static const uint8_t CMD_REFRESH    = 0b0001;
    static const uint8_t CMD_MRS        = 0b0000;
    static const uint8_t CMD_BST        = 0b0110;

private:
    // Memory array
    uint16_t* mem;

    // Bank state
    uint16_t active_row[NUM_BANKS];
    bool row_active[NUM_BANKS];

    // Mode register
    int cas_latency;
    int burst_length;
    bool burst_type_interleaved;

    // Read pipeline for CAS latency
    uint16_t read_pipe_data[4];
    bool read_pipe_valid[4];
    uint8_t read_pipe_dqm[4];

    // Output state
    bool output_enable;
    uint16_t dq_out;

    // Debug
    bool debug_enabled;

public:
    SDRAMModelCpp(bool debug = false) {
        mem = new uint16_t[SIZE_WORDS];
        debug_enabled = debug;
        reset();
    }

    ~SDRAMModelCpp() {
        delete[] mem;
    }

    void reset() {
        memset(mem, 0, SIZE_WORDS * sizeof(uint16_t));
        for (int i = 0; i < NUM_BANKS; i++) {
            active_row[i] = 0;
            row_active[i] = false;
        }
        cas_latency = CAS_LATENCY_2;
        burst_length = 1;
        burst_type_interleaved = false;

        for (int i = 0; i < 4; i++) {
            read_pipe_data[i] = 0;
            read_pipe_valid[i] = false;
            read_pipe_dqm[i] = 0;
        }

        output_enable = false;
        dq_out = 0;
    }

    // Main tick function - call every clock cycle
    // Returns data to drive on DQ bus (0xFFFF means high-Z)
    uint16_t tick(
        bool cs_n,      // Chip select (active low)
        bool ras_n,     // RAS (active low)
        bool cas_n,     // CAS (active low)
        bool we_n,      // WE (active low)
        uint8_t ba,     // Bank address (2 bits)
        uint16_t addr,  // Address (13 bits used)
        uint8_t dqm,    // Data mask (2 bits, active high)
        uint16_t dq_in  // Data input (for writes)
    ) {
        // Shift read pipeline
        for (int i = 3; i > 0; i--) {
            read_pipe_data[i] = read_pipe_data[i-1];
            read_pipe_valid[i] = read_pipe_valid[i-1];
            read_pipe_dqm[i] = read_pipe_dqm[i-1];
        }
        read_pipe_valid[0] = false;
        read_pipe_dqm[0] = 0;

        // Output based on CAS latency
        // CAS latency defines cycles after READ command until data appears
        // Pipeline: [0] at READ, [1] after 1 cycle, [2] after 2 cycles, [3] after 3 cycles
        int pipe_idx = cas_latency;  // CAS=2 uses [2], CAS=3 uses [3]
        output_enable = read_pipe_valid[pipe_idx];
        if (output_enable) {
            uint8_t mask = read_pipe_dqm[pipe_idx];
            dq_out = read_pipe_data[pipe_idx];
            // Apply DQM - masked bytes are high-Z (we return the data anyway)
        }

        // Process command if chip selected
        if (!cs_n) {
            uint8_t cmd = (ras_n << 2) | (cas_n << 1) | we_n;

            switch (cmd) {
                case CMD_ACTIVE:
                    handleActivate(ba, addr);
                    break;

                case CMD_READ:
                    handleRead(ba, addr, dqm);
                    break;

                case CMD_WRITE:
                    handleWrite(ba, addr, dqm, dq_in);
                    break;

                case CMD_PRECHARGE:
                    handlePrecharge(ba, addr);
                    break;

                case CMD_REFRESH:
                    handleRefresh();
                    break;

                case CMD_MRS:
                    handleMRS(addr);
                    break;

                case CMD_BST:
                    handleBurstStop();
                    break;

                case CMD_NOP:
                default:
                    // No operation
                    break;
            }
        }

        return output_enable ? dq_out : 0xFFFF;
    }

    // Check if output is enabled (for tri-state control)
    bool isOutputEnabled() const {
        return output_enable;
    }

    // Direct memory access
    uint16_t peek(uint32_t word_addr) const {
        if (word_addr < SIZE_WORDS) {
            return mem[word_addr];
        }
        return 0;
    }

    void poke(uint32_t word_addr, uint16_t data) {
        if (word_addr < SIZE_WORDS) {
            mem[word_addr] = data;
        }
    }

    // Byte access
    uint8_t peekByte(uint32_t byte_addr) const {
        uint16_t word = peek(byte_addr >> 1);
        return (byte_addr & 1) ? (word >> 8) : (word & 0xFF);
    }

    void pokeByte(uint32_t byte_addr, uint8_t data) {
        uint32_t word_addr = byte_addr >> 1;
        if (word_addr < SIZE_WORDS) {
            if (byte_addr & 1) {
                mem[word_addr] = (mem[word_addr] & 0x00FF) | ((uint16_t)data << 8);
            } else {
                mem[word_addr] = (mem[word_addr] & 0xFF00) | data;
            }
        }
    }

    // Load binary file
    int loadBinary(const char* filename, uint32_t start_addr = 0) {
        FILE* f = fopen(filename, "rb");
        if (!f) {
            if (debug_enabled) printf("SDRAM: Cannot open %s\n", filename);
            return -1;
        }

        fseek(f, 0, SEEK_END);
        size_t size = ftell(f);
        fseek(f, 0, SEEK_SET);

        uint8_t buffer[1024];
        uint32_t addr = start_addr;
        size_t total = 0;

        while (total < size) {
            size_t chunk = fread(buffer, 1, sizeof(buffer), f);
            if (chunk == 0) break;

            for (size_t i = 0; i < chunk; i++) {
                pokeByte(addr++, buffer[i]);
            }
            total += chunk;
        }

        fclose(f);
        if (debug_enabled) printf("SDRAM: Loaded %zu bytes from %s at 0x%08X\n", total, filename, start_addr);
        return (int)total;
    }

    // Save to binary file
    int saveBinary(const char* filename, uint32_t start_addr, uint32_t size) {
        FILE* f = fopen(filename, "wb");
        if (!f) return -1;

        for (uint32_t i = 0; i < size; i++) {
            uint8_t b = peekByte(start_addr + i);
            fwrite(&b, 1, 1, f);
        }

        fclose(f);
        return (int)size;
    }

    // Dump memory region
    void dump(uint32_t addr, uint32_t size) {
        printf("SDRAM Dump [0x%08X - 0x%08X]:\n", addr, addr + size - 1);
        for (uint32_t i = 0; i < size; i += 16) {
            printf("  %08X: ", addr + i);
            for (uint32_t j = 0; j < 16 && i + j < size; j += 2) {
                printf("%04X ", peek((addr + i + j) >> 1));
            }
            printf("\n");
        }
    }

    // Fill region
    void fill(uint32_t addr, uint32_t size, uint16_t value) {
        for (uint32_t i = 0; i < size / 2; i++) {
            poke((addr >> 1) + i, value);
        }
    }

    // Clear all memory
    void clear() {
        memset(mem, 0, SIZE_WORDS * sizeof(uint16_t));
    }

    // Get raw memory pointer (for direct access)
    uint16_t* getMemoryPointer() {
        return mem;
    }

private:
    uint32_t calcAddr(uint8_t bank, uint16_t row, uint16_t col) {
        // Reconstruct user word address from bank/row/col
        // Gameboy controller addressing:
        // - Bank: user_addr[21:20]
        // - Row: user_addr[19:8]
        // - Col: {user_addr[22], user_addr[7:0]}
        // Reconstruction: user_addr = (bank << 20) | (row << 8) | col_bits
        uint32_t user_addr = ((uint32_t)(bank & 3) << 20) |
                             ((uint32_t)(row & 0xFFF) << 8) |
                             (col & 0xFF);
        // Handle bit 22 which is encoded in col[8]
        if (col & 0x100) {
            user_addr |= (1 << 22);
        }
        return user_addr;
    }

    void handleActivate(uint8_t bank, uint16_t addr) {
        active_row[bank & 3] = addr & 0x1FFF;
        row_active[bank & 3] = true;
        if (debug_enabled) {
            printf("SDRAM: ACTIVATE bank=%d row=0x%04X\n", bank & 3, addr & 0x1FFF);
        }
    }

    void handleRead(uint8_t bank, uint16_t addr, uint8_t dqm) {
        bank &= 3;
        if (!row_active[bank]) {
            if (debug_enabled) printf("SDRAM: ERROR - READ to inactive bank %d\n", bank);
            return;
        }

        uint16_t col = addr & 0x3FF;
        uint32_t mem_addr = calcAddr(bank, active_row[bank], col);
        uint16_t data = (mem_addr < SIZE_WORDS) ? mem[mem_addr] : 0;

        // Insert into pipeline
        read_pipe_data[0] = data;
        read_pipe_valid[0] = true;
        read_pipe_dqm[0] = dqm;

        if (debug_enabled) {
            printf("SDRAM: READ bank=%d col=0x%03X addr=0x%08X data=0x%04X\n",
                   bank, col, mem_addr, data);
        }

        // Auto-precharge if A10 set
        if (addr & 0x400) {
            row_active[bank] = false;
            if (debug_enabled) printf("SDRAM: AUTO-PRECHARGE bank=%d\n", bank);
        }
    }

    void handleWrite(uint8_t bank, uint16_t addr, uint8_t dqm, uint16_t data) {
        bank &= 3;
        if (!row_active[bank]) {
            if (debug_enabled) printf("SDRAM: ERROR - WRITE to inactive bank %d\n", bank);
            return;
        }

        uint16_t col = addr & 0x3FF;
        uint32_t mem_addr = calcAddr(bank, active_row[bank], col);

        if (mem_addr < SIZE_WORDS) {
            // Apply byte mask (DQM active high = mask)
            if (!(dqm & 1)) mem[mem_addr] = (mem[mem_addr] & 0xFF00) | (data & 0x00FF);
            if (!(dqm & 2)) mem[mem_addr] = (mem[mem_addr] & 0x00FF) | (data & 0xFF00);
        }

        if (debug_enabled) {
            printf("SDRAM: WRITE bank=%d col=0x%03X addr=0x%08X data=0x%04X dqm=%d%d\n",
                   bank, col, mem_addr, data, (dqm >> 1) & 1, dqm & 1);
        }

        // Auto-precharge if A10 set
        if (addr & 0x400) {
            row_active[bank] = false;
            if (debug_enabled) printf("SDRAM: AUTO-PRECHARGE bank=%d\n", bank);
        }
    }

    void handlePrecharge(uint8_t bank, uint16_t addr) {
        if (addr & 0x400) {
            // Precharge all banks
            for (int i = 0; i < NUM_BANKS; i++) {
                row_active[i] = false;
            }
            if (debug_enabled) printf("SDRAM: PRECHARGE ALL\n");
        } else {
            row_active[bank & 3] = false;
            if (debug_enabled) printf("SDRAM: PRECHARGE bank=%d\n", bank & 3);
        }
    }

    void handleRefresh() {
        // Auto refresh - all rows closed
        for (int i = 0; i < NUM_BANKS; i++) {
            row_active[i] = false;
        }
        if (debug_enabled) printf("SDRAM: AUTO REFRESH\n");
    }

    void handleMRS(uint16_t addr) {
        burst_length = 1 << (addr & 7);
        if (burst_length > 8) burst_length = 256; // Full page
        burst_type_interleaved = (addr >> 3) & 1;
        cas_latency = (addr >> 4) & 7;
        if (cas_latency < 2) cas_latency = 2;
        if (cas_latency > 3) cas_latency = 3;

        if (debug_enabled) {
            printf("SDRAM: MRS - BL=%d, BT=%s, CL=%d\n",
                   burst_length,
                   burst_type_interleaved ? "interleaved" : "sequential",
                   cas_latency);
        }
    }

    void handleBurstStop() {
        output_enable = false;
        for (int i = 0; i < 4; i++) {
            read_pipe_valid[i] = false;
        }
        if (debug_enabled) printf("SDRAM: BURST STOP\n");
    }
};

#endif // SDRAM_MODEL_CPP_H
