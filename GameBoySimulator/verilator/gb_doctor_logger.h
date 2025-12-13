// gb_doctor_logger.h - GameBoy Doctor CPU State Logger
// Captures CPU execution trace in gameboy-doctor format for debugging
// Format: A:XX F:XX B:XX C:XX D:XX E:XX H:XX L:XX SP:XXXX PC:XXXX PCMEM:XX,XX,XX,XX

#ifndef GB_DOCTOR_LOGGER_H
#define GB_DOCTOR_LOGGER_H

#include <cstdio>
#include <cstdint>
#include <string>
#include "../sim/mister_sdram_model.h"

class GBDoctorLogger {
private:
    FILE* log_file;
    bool enabled;
    bool logging_started;
    uint16_t prev_pc;
    uint64_t instruction_count;
    bool debug;
    uint8_t boot_rom[256];  // Copy of boot ROM for PCMEM reading
    bool boot_rom_available;

public:
    GBDoctorLogger(const char* filename = nullptr, bool debug_mode = false)
        : log_file(nullptr)
        , enabled(false)
        , logging_started(false)
        , prev_pc(0)
        , instruction_count(0)
        , debug(debug_mode)
        , boot_rom_available(false)
    {
        memset(boot_rom, 0, sizeof(boot_rom));
        if (filename) {
            log_file = fopen(filename, "w");
            if (!log_file) {
                fprintf(stderr, "Failed to open log file: %s\n", filename);
            } else {
                if (debug) printf("GBDoctorLogger: Opened log file %s\n", filename);
            }
        }
    }

    ~GBDoctorLogger() {
        if (log_file) {
            fclose(log_file);
        }
    }

    // Enable/disable logging
    void set_enabled(bool enable) {
        enabled = enable;
        if (enable && !logging_started) {
            logging_started = true;
            if (debug) printf("GBDoctorLogger: Logging started\n");
        }
    }

    bool is_enabled() const {
        return enabled;
    }

    // Store a copy of boot ROM for PCMEM reading
    void set_boot_rom(const uint8_t* rom, size_t size) {
        if (size > 256) size = 256;
        memcpy(boot_rom, rom, size);
        if (size < 256) memset(boot_rom + size, 0, 256 - size);
        boot_rom_available = true;
        if (debug) printf("GBDoctorLogger: Boot ROM copy stored (%zu bytes)\n", size);
    }

    // Main tick function - call every clock cycle
    // DUT is the Verilated design under test (top module)
    template<typename DUT>
    void tick(DUT* dut, MisterSDRAMModel* sdram) {
        if (!enabled || !log_file) return;

        // Detect instruction boundary:
        // For this GameBoy core, M-cycle stays constant at 1, so we use PC changes
        // Each time PC changes, a new instruction has started
        uint16_t curr_pc = dut->dbg_cpu_pc;

        // Instruction boundary = PC change
        bool instruction_complete = (curr_pc != prev_pc) && (prev_pc != 0);

        if (instruction_complete) {
            // Log the state AT the new PC
            // The PC has advanced to the next instruction
            log_state(dut, sdram, curr_pc);
        }

        prev_pc = curr_pc;
    }

    // Log CPU state in gameboy-doctor format
    template<typename DUT>
    void log_state(DUT* dut, MisterSDRAMModel* sdram, uint16_t pc) {
        if (!log_file) return;

        // Extract registers from debug signals
        uint8_t a = (dut->dbg_cpu_acc) & 0xFF;
        uint8_t f = (dut->dbg_cpu_f) & 0xFF;

        // BC, DE, HL are 16-bit pairs
        uint16_t bc = dut->dbg_cpu_bc;
        uint8_t b = (bc >> 8) & 0xFF;
        uint8_t c = bc & 0xFF;

        uint16_t de = dut->dbg_cpu_de;
        uint8_t d = (de >> 8) & 0xFF;
        uint8_t e = de & 0xFF;

        uint16_t hl = dut->dbg_cpu_hl;
        uint8_t h = (hl >> 8) & 0xFF;
        uint8_t l = hl & 0xFF;

        uint16_t sp = dut->dbg_cpu_sp;

        // Read PCMEM (4 bytes at PC)
        uint8_t pcmem[4];
        read_pcmem(dut, sdram, pc, pcmem);

        // Format: A:XX F:XX B:XX C:XX D:XX E:XX H:XX L:XX SP:XXXX PC:XXXX PCMEM:XX,XX,XX,XX
        fprintf(log_file, "A:%02X F:%02X B:%02X C:%02X D:%02X E:%02X H:%02X L:%02X SP:%04X PC:%04X PCMEM:%02X,%02X,%02X,%02X\n",
            a, f, b, c, d, e, h, l, sp, pc,
            pcmem[0], pcmem[1], pcmem[2], pcmem[3]);

        instruction_count++;

        if (debug && (instruction_count % 1000 == 0)) {
            printf("GBDoctorLogger: Logged %lu instructions\n", (unsigned long)instruction_count);
        }
    }

    // Read 4 bytes of memory at PC for PCMEM field
    template<typename DUT>
    void read_pcmem(DUT* dut, MisterSDRAMModel* sdram, uint16_t pc, uint8_t* out) {
        // GameBoy memory map:
        // 0x0000-0x00FF: Boot ROM (if enabled) or Cart ROM
        // 0x0100-0x7FFF: Cart ROM
        // 0x8000-0x9FFF: VRAM
        // 0xA000-0xBFFF: Cart RAM
        // 0xC000-0xDFFF: Work RAM
        // 0xE000-0xFDFF: Echo RAM
        // 0xFE00-0xFE9F: OAM
        // 0xFEA0-0xFEFF: Prohibited
        // 0xFF00-0xFF7F: I/O Registers
        // 0xFF80-0xFFFE: High RAM
        // 0xFFFF: IE Register

        for (int i = 0; i < 4; i++) {
            uint16_t addr = (pc + i) & 0xFFFF;

            // Check if address is in boot ROM range and boot ROM is enabled
            if (addr < 0x0100 && dut->dbg_boot_rom_enabled && boot_rom_available) {
                // Read from boot ROM copy
                out[i] = boot_rom[addr];
            } else if (addr < 0x8000) {
                // Cart ROM area - read from SDRAM
                out[i] = sdram->read_byte(addr);
            } else if (addr >= 0x8000 && addr < 0xA000) {
                // VRAM - read from SDRAM
                out[i] = sdram->read_byte(addr);
            } else if (addr >= 0xC000 && addr < 0xE000) {
                // Work RAM - read from SDRAM
                out[i] = sdram->read_byte(addr);
            } else {
                // I/O, OAM, HRAM - not in SDRAM, return 0
                out[i] = 0x00;
            }
        }
    }

    // Get statistics
    uint64_t get_instruction_count() const {
        return instruction_count;
    }

    // Flush log file
    void flush() {
        if (log_file) {
            fflush(log_file);
        }
    }

    // Reset logger state
    void reset() {
        prev_pc = 0;
        instruction_count = 0;
        logging_started = false;
    }
};

#endif // GB_DOCTOR_LOGGER_H
