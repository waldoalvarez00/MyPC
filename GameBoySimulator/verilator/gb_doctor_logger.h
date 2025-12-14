// gb_doctor_logger.h - GameBoy Doctor CPU State Logger
// Captures CPU execution trace in gameboy-doctor format for debugging
// Format: A:XX F:XX B:XX C:XX D:XX E:XX H:XX L:XX SP:XXXX PC:XXXX PCMEM:XX,XX,XX,XX

#ifndef GB_DOCTOR_LOGGER_H
#define GB_DOCTOR_LOGGER_H

#include <cstdio>
#include <cstdint>
#include <string>
#include "../sim/mister_sdram_model.h"
// For accessing internal WRAM dpram
#include "Vtop.h"
#include "Vtop_top.h"
#include "Vtop_gb.h"
#include "Vtop_dpram__Af.h"

class GBDoctorLogger {
private:
    FILE* log_file;
    bool enabled;
    bool logging_started;
    uint16_t prev_pc;
    uint8_t prev_mcycle;   // Previous M-cycle for detecting instruction boundaries
    uint8_t prev_tstate;   // Previous T-state for detecting M1/T1 start
    uint16_t m1_pc;        // PC captured at M1/T1 (instruction address before increment)
    uint64_t instruction_count;
    bool debug;
    uint8_t boot_rom[256];  // Copy of boot ROM for PCMEM reading
    bool boot_rom_available;
    bool first_log_done;   // Track if initial state was logged
    bool skip_next_m1t4;   // Skip the next M1/T4 detection (after log_initial_state)
    bool pending_log;      // Flag set at M1/T1, log happens at M1/T2

public:
    GBDoctorLogger(const char* filename = nullptr, bool debug_mode = false)
        : log_file(nullptr)
        , enabled(false)
        , logging_started(false)
        , prev_pc(0)
        , prev_mcycle(0)
        , prev_tstate(0)
        , m1_pc(0)
        , instruction_count(0)
        , debug(debug_mode)
        , boot_rom_available(false)
        , first_log_done(false)
        , skip_next_m1t4(false)
        , pending_log(false)
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
            first_log_done = true;  // Auto-enable logging (no manual initial state needed)
            if (debug) printf("GBDoctorLogger: Logging started\n");
        }
    }

    // Log initial state immediately (call when first enabling at start PC)
    // This captures the state BEFORE the first instruction executes
    template<typename DUT>
    void log_initial_state(DUT* dut, MisterSDRAMModel* sdram) {
        if (!log_file) return;
        uint16_t curr_pc = dut->dbg_cpu_pc;
        log_state(dut, sdram, curr_pc);
        // Update state - this prevents duplicate logging in tick() because
        // the transition detection will see prev_mcycle == curr_mcycle
        prev_pc = curr_pc;
        prev_mcycle = dut->dbg_cpu_mcycle;
        prev_tstate = dut->dbg_cpu_tstate;
        m1_pc = curr_pc;
        first_log_done = true;
        // Don't set skip_next_m1t4 - the prev_mcycle update already prevents
        // duplicate logging, and setting it would incorrectly skip the NEXT instruction
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

        // Detect instruction boundary using M-cycle transitions:
        // GameBoy CPU T-state encoding: 2=T1, 4=T2, 8=T3, 16=T4
        // M-cycle values: 1=M1 (opcode fetch), 2=M2, 4=M3/M4
        //
        // A new instruction starts when:
        // - M-cycle TRANSITIONS from non-1 (2 or 4) to 1
        // - This marks the start of a new instruction's opcode fetch
        //
        // Important: mcycle can stay at 1 for multiple T-state cycles during
        // extended opcode fetch (e.g., for multi-byte instructions), so we must
        // detect the TRANSITION, not just mcycle==1.
        uint8_t curr_mcycle = dut->dbg_cpu_mcycle;
        uint8_t curr_tstate = dut->dbg_cpu_tstate;
        uint16_t curr_pc = dut->dbg_cpu_pc;

        // Instruction boundary detection:
        // A new instruction starts when mcycle=1 and tstate=2 (M1/T1), but we need to
        // distinguish between:
        // 1. New instruction after multi-cycle instruction: mcycle transitions 2/4 → 1
        // 2. New instruction after single-cycle instruction: mcycle stays at 1, tstate wraps 16 → 2
        //
        // Key insight: The transition from tstate=16 to tstate=2 while mcycle=1 marks
        // a new instruction boundary (either mcycle changed to 1, or it stayed at 1 after
        // a single-cycle instruction completed).
        //
        // IMPORTANT: Log at M1/T2 (tstate=4) instead of M1/T1 to ensure registers from
        // the previous instruction have settled. The register file updates on the clock
        // edge, so logging at T1 might capture stale register values.

        // Track when we detect a new instruction start (at M1/T1)
        bool at_m1_t1 = (curr_mcycle == 1 && curr_tstate == 2);
        bool at_m1_t2 = (curr_mcycle == 1 && curr_tstate == 4);

        // New instruction boundary at M1/T1 when:
        // 1. mcycle transitioned from non-1 to 1 (multi-cycle instruction completed)
        // 2. OR tstate wrapped to 2 while mcycle stays at 1 (single-cycle instruction)
        //    Note: tstate can wrap from T4 (16), T5 (32), or T6 (64) depending on instruction
        //    e.g., INC HL has 6 T-states, so prev_tstate=64 before wrap
        // 3. OR first tick after reset (prev_mcycle=0)
        bool mcycle_transition = (curr_mcycle == 1 && prev_mcycle != 1 && prev_mcycle != 0);
        // Check for any high tstate (T4/T5/T6) wrapping to T1 while staying in M1
        bool tstate_wrap = (prev_tstate >= 16 && curr_tstate == 2 && curr_mcycle == 1 && prev_mcycle == 1);
        bool first_m1_after_reset = (prev_mcycle == 0 && curr_mcycle == 1 && curr_tstate == 2);

        // At M1/T1: capture PC and set flag for logging at T2
        if (at_m1_t1 && (mcycle_transition || tstate_wrap || first_m1_after_reset)) {
            m1_pc = curr_pc;  // Save instruction PC for logging at T2
            pending_log = true;
        }

        // At M1/T2: log the state (registers have settled from previous instruction)
        if (at_m1_t2 && pending_log && first_log_done) {
            pending_log = false;
            if (skip_next_m1t4) {
                // Skip this log (initial state was already logged manually)
                skip_next_m1t4 = false;
            } else {
                // Log state with the PC captured at M1/T1
                log_state(dut, sdram, m1_pc);
            }
        }

        prev_mcycle = curr_mcycle;
        prev_tstate = curr_tstate;
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
                // Work RAM - read from internal WRAM dpram
                // DMG mode: 8KB WRAM at 0xC000-0xDFFF, use lower 13 bits
                // Address mapping: wram_addr = addr & 0x1FFF
                uint16_t wram_offset = addr & 0x1FFF;
                out[i] = dut->top->gameboy->wram->mem[wram_offset];
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
        prev_mcycle = 0;
        prev_tstate = 0;
        m1_pc = 0;
        instruction_count = 0;
        logging_started = false;
        first_log_done = false;
        skip_next_m1t4 = false;
        pending_log = false;
    }
};

#endif // GB_DOCTOR_LOGGER_H
