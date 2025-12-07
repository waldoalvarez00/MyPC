// ROM Loader Model for Verilator Simulation
// Loads ROM files and transfers to SDRAM model
//
// Supports:
// - Binary ROM files (.bin, .gb, .gbc)
// - Intel HEX format (.hex)
// - Direct memory transfer to SDRAM model
//
// Gameboy ROM structure:
// - 0x0000-0x3FFF: ROM Bank 0 (fixed)
// - 0x4000-0x7FFF: ROM Bank 1-N (switchable)
// - Header at 0x0100-0x014F

#ifndef ROM_LOADER_H
#define ROM_LOADER_H

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

class ROMLoader {
public:
    // ROM size limits
    static const uint32_t MAX_ROM_SIZE = 8 * 1024 * 1024;  // 8 MB max
    static const uint32_t GB_BANK_SIZE = 16 * 1024;        // 16 KB per bank

    // Gameboy header offsets
    static const int GB_HEADER_START = 0x0100;
    static const int GB_TITLE_OFFSET = 0x0134;
    static const int GB_CGB_FLAG = 0x0143;
    static const int GB_CART_TYPE = 0x0147;
    static const int GB_ROM_SIZE = 0x0148;
    static const int GB_RAM_SIZE = 0x0149;
    static const int GB_CHECKSUM = 0x014D;

    // ROM info structure
    struct ROMInfo {
        std::string filename;
        std::string title;
        uint32_t size;
        uint32_t num_banks;
        uint8_t cart_type;
        uint8_t rom_size_code;
        uint8_t ram_size_code;
        bool is_cgb;           // Color Gameboy
        bool is_sgb;           // Super Gameboy
        uint8_t header_checksum;
        bool valid;
    };

    // Transfer state
    enum TransferState {
        IDLE,
        TRANSFERRING,
        COMPLETE,
        ERROR
    };

private:
    // ROM buffer
    std::vector<uint8_t> rom_data;
    ROMInfo info;

    // Transfer state
    TransferState state;
    uint32_t transfer_addr;
    uint32_t bytes_transferred;
    uint32_t target_addr;

    // Configuration
    bool debug_enabled;

public:
    ROMLoader(bool debug = false)
        : debug_enabled(debug) {
        reset();
    }

    void reset() {
        rom_data.clear();
        info = {};
        state = IDLE;
        transfer_addr = 0;
        bytes_transferred = 0;
        target_addr = 0;
    }

    // Load ROM from binary file
    bool loadBinary(const char* filename, uint32_t max_size = MAX_ROM_SIZE) {
        reset();

        FILE* f = fopen(filename, "rb");
        if (!f) {
            if (debug_enabled) printf("ROM: Cannot open %s\n", filename);
            state = ERROR;
            return false;
        }

        // Get file size
        fseek(f, 0, SEEK_END);
        size_t size = ftell(f);
        fseek(f, 0, SEEK_SET);

        if (size > max_size) {
            if (debug_enabled) printf("ROM: File too large (%zu > %u)\n", size, max_size);
            fclose(f);
            state = ERROR;
            return false;
        }

        // Read file
        rom_data.resize(size);
        size_t read = fread(rom_data.data(), 1, size, f);
        fclose(f);

        if (read != size) {
            if (debug_enabled) printf("ROM: Read error (%zu of %zu bytes)\n", read, size);
            state = ERROR;
            return false;
        }

        // Parse ROM info
        info.filename = filename;
        info.size = (uint32_t)size;
        info.num_banks = (uint32_t)((size + GB_BANK_SIZE - 1) / GB_BANK_SIZE);
        info.valid = true;

        // Parse Gameboy header if ROM is large enough
        if (size >= 0x0150) {
            parseGameboyHeader();
        }

        if (debug_enabled) {
            printf("ROM: Loaded %s (%u bytes, %u banks)\n",
                   filename, info.size, info.num_banks);
            if (!info.title.empty()) {
                printf("ROM: Title: %s\n", info.title.c_str());
            }
        }

        return true;
    }

    // Load ROM from Intel HEX file
    bool loadIntelHex(const char* filename) {
        reset();

        FILE* f = fopen(filename, "r");
        if (!f) {
            if (debug_enabled) printf("ROM: Cannot open %s\n", filename);
            state = ERROR;
            return false;
        }

        // Reserve space for ROM data
        rom_data.resize(MAX_ROM_SIZE, 0xFF);
        uint32_t max_addr = 0;
        uint32_t base_addr = 0;

        char line[256];
        int line_num = 0;

        while (fgets(line, sizeof(line), f)) {
            line_num++;

            // Skip empty lines
            if (line[0] != ':') continue;

            // Parse Intel HEX record
            uint8_t byte_count, record_type, checksum;
            uint16_t address;

            if (sscanf(line + 1, "%02hhx%04hx%02hhx",
                       &byte_count, &address, &record_type) != 3) {
                if (debug_enabled) printf("ROM: Parse error at line %d\n", line_num);
                continue;
            }

            // Calculate checksum
            uint8_t sum = byte_count + (address >> 8) + (address & 0xFF) + record_type;

            // Parse data bytes
            std::vector<uint8_t> data(byte_count);
            for (int i = 0; i < byte_count; i++) {
                if (sscanf(line + 9 + i * 2, "%02hhx", &data[i]) != 1) {
                    if (debug_enabled) printf("ROM: Data parse error at line %d\n", line_num);
                    break;
                }
                sum += data[i];
            }

            // Parse checksum
            sscanf(line + 9 + byte_count * 2, "%02hhx", &checksum);
            sum += checksum;

            if (sum != 0) {
                if (debug_enabled) printf("ROM: Checksum error at line %d\n", line_num);
            }

            // Process record
            switch (record_type) {
                case 0x00:  // Data record
                    for (int i = 0; i < byte_count; i++) {
                        uint32_t addr = base_addr + address + i;
                        if (addr < MAX_ROM_SIZE) {
                            rom_data[addr] = data[i];
                            if (addr > max_addr) max_addr = addr;
                        }
                    }
                    break;

                case 0x01:  // End of file
                    break;

                case 0x02:  // Extended segment address
                    if (byte_count >= 2) {
                        base_addr = ((uint32_t)data[0] << 12) | ((uint32_t)data[1] << 4);
                    }
                    break;

                case 0x04:  // Extended linear address
                    if (byte_count >= 2) {
                        base_addr = ((uint32_t)data[0] << 24) | ((uint32_t)data[1] << 16);
                    }
                    break;

                default:
                    break;
            }
        }

        fclose(f);

        // Trim ROM data to actual size
        rom_data.resize(max_addr + 1);

        info.filename = filename;
        info.size = (uint32_t)rom_data.size();
        info.num_banks = (uint32_t)((info.size + GB_BANK_SIZE - 1) / GB_BANK_SIZE);
        info.valid = true;

        if (debug_enabled) {
            printf("ROM: Loaded Intel HEX %s (%u bytes)\n", filename, info.size);
        }

        return true;
    }

    // Get ROM info
    const ROMInfo& getInfo() const {
        return info;
    }

    // Get ROM size
    uint32_t getSize() const {
        return (uint32_t)rom_data.size();
    }

    // Get ROM data pointer
    const uint8_t* getData() const {
        return rom_data.data();
    }

    // Read byte from ROM
    uint8_t readByte(uint32_t addr) const {
        if (addr < rom_data.size()) {
            return rom_data[addr];
        }
        return 0xFF;
    }

    // Read word from ROM (little-endian)
    uint16_t readWord(uint32_t addr) const {
        return readByte(addr) | ((uint16_t)readByte(addr + 1) << 8);
    }

    // Start transfer to memory
    void startTransfer(uint32_t dest_addr = 0) {
        target_addr = dest_addr;
        transfer_addr = 0;
        bytes_transferred = 0;
        state = TRANSFERRING;

        if (debug_enabled) {
            printf("ROM: Starting transfer to 0x%08X (%u bytes)\n",
                   dest_addr, (uint32_t)rom_data.size());
        }
    }

    // Get next byte to transfer
    // Returns true if transfer is in progress
    bool getNextByte(uint32_t& addr, uint8_t& data) {
        if (state != TRANSFERRING) {
            return false;
        }

        if (transfer_addr >= rom_data.size()) {
            state = COMPLETE;
            if (debug_enabled) {
                printf("ROM: Transfer complete (%u bytes)\n", bytes_transferred);
            }
            return false;
        }

        addr = target_addr + transfer_addr;
        data = rom_data[transfer_addr];
        transfer_addr++;
        bytes_transferred++;

        return true;
    }

    // Get next word to transfer (for 16-bit bus)
    bool getNextWord(uint32_t& addr, uint16_t& data) {
        if (state != TRANSFERRING) {
            return false;
        }

        if (transfer_addr >= rom_data.size()) {
            state = COMPLETE;
            if (debug_enabled) {
                printf("ROM: Transfer complete (%u bytes)\n", bytes_transferred);
            }
            return false;
        }

        addr = target_addr + transfer_addr;

        // Read word (little-endian)
        uint8_t lo = rom_data[transfer_addr];
        uint8_t hi = (transfer_addr + 1 < rom_data.size()) ?
                     rom_data[transfer_addr + 1] : 0xFF;
        data = lo | ((uint16_t)hi << 8);

        transfer_addr += 2;
        bytes_transferred += 2;

        return true;
    }

    // Check transfer state
    TransferState getState() const {
        return state;
    }

    bool isTransferring() const {
        return state == TRANSFERRING;
    }

    bool isComplete() const {
        return state == COMPLETE;
    }

    uint32_t getBytesTransferred() const {
        return bytes_transferred;
    }

    // Get transfer progress (0-100)
    int getProgress() const {
        if (rom_data.empty()) return 0;
        return (int)(bytes_transferred * 100 / rom_data.size());
    }

    // Generate test ROM with known pattern
    void generateTestROM(uint32_t size, uint8_t pattern = 0) {
        reset();
        rom_data.resize(size);

        for (uint32_t i = 0; i < size; i++) {
            if (pattern == 0) {
                // Incrementing pattern
                rom_data[i] = (uint8_t)(i & 0xFF);
            } else if (pattern == 1) {
                // Address-based pattern (good for testing)
                rom_data[i] = (uint8_t)((i ^ (i >> 8) ^ (i >> 16)) & 0xFF);
            } else if (pattern == 2) {
                // Gameboy-like pattern with header
                if (i >= 0x0104 && i < 0x0134) {
                    // Nintendo logo (simplified)
                    rom_data[i] = 0xCE;
                } else if (i >= 0x0134 && i < 0x0144) {
                    // Title "TEST"
                    const char* title = "TEST ROM";
                    int idx = i - 0x0134;
                    rom_data[i] = (idx < 8) ? title[idx] : 0;
                } else if (i == 0x0147) {
                    rom_data[i] = 0x00;  // ROM only
                } else if (i == 0x0148) {
                    // ROM size code
                    if (size <= 32 * 1024) rom_data[i] = 0;
                    else if (size <= 64 * 1024) rom_data[i] = 1;
                    else if (size <= 128 * 1024) rom_data[i] = 2;
                    else if (size <= 256 * 1024) rom_data[i] = 3;
                    else rom_data[i] = 4;
                } else {
                    rom_data[i] = (uint8_t)(i & 0xFF);
                }
            } else {
                rom_data[i] = pattern;
            }
        }

        info.filename = "generated";
        info.size = size;
        info.num_banks = (size + GB_BANK_SIZE - 1) / GB_BANK_SIZE;
        info.valid = true;

        if (size >= 0x0150 && pattern == 2) {
            parseGameboyHeader();
        }

        if (debug_enabled) {
            printf("ROM: Generated test ROM (%u bytes, pattern %d)\n", size, pattern);
        }
    }

    // Verify ROM data against memory
    int verifyAgainstMemory(const uint8_t* mem, uint32_t mem_size, uint32_t start_addr = 0) {
        int errors = 0;

        for (uint32_t i = 0; i < rom_data.size(); i++) {
            uint32_t mem_addr = start_addr + i;
            if (mem_addr >= mem_size) break;

            if (mem[mem_addr] != rom_data[i]) {
                if (debug_enabled && errors < 10) {
                    printf("ROM: Verify error at 0x%08X: expected 0x%02X, got 0x%02X\n",
                           mem_addr, rom_data[i], mem[mem_addr]);
                }
                errors++;
            }
        }

        if (debug_enabled) {
            if (errors == 0) {
                printf("ROM: Verification passed (%u bytes)\n", (uint32_t)rom_data.size());
            } else {
                printf("ROM: Verification failed with %d errors\n", errors);
            }
        }

        return errors;
    }

    // Dump ROM header info
    void dumpInfo() const {
        printf("ROM Information:\n");
        printf("  Filename: %s\n", info.filename.c_str());
        printf("  Size: %u bytes (%u banks)\n", info.size, info.num_banks);
        if (!info.title.empty()) {
            printf("  Title: %s\n", info.title.c_str());
            printf("  Cart Type: 0x%02X\n", info.cart_type);
            printf("  ROM Size Code: 0x%02X\n", info.rom_size_code);
            printf("  RAM Size Code: 0x%02X\n", info.ram_size_code);
            printf("  CGB: %s\n", info.is_cgb ? "Yes" : "No");
            printf("  SGB: %s\n", info.is_sgb ? "Yes" : "No");
            printf("  Header Checksum: 0x%02X\n", info.header_checksum);
        }
    }

private:
    void parseGameboyHeader() {
        if (rom_data.size() < 0x0150) return;

        // Extract title (up to 16 characters)
        char title[17] = {0};
        for (int i = 0; i < 16; i++) {
            uint8_t c = rom_data[GB_TITLE_OFFSET + i];
            if (c == 0 || c >= 0x80) break;
            title[i] = (char)c;
        }
        info.title = title;

        // CGB flag
        uint8_t cgb = rom_data[GB_CGB_FLAG];
        info.is_cgb = (cgb == 0x80 || cgb == 0xC0);

        // SGB flag
        info.is_sgb = (rom_data[0x0146] == 0x03);

        // Cart type
        info.cart_type = rom_data[GB_CART_TYPE];

        // ROM/RAM size codes
        info.rom_size_code = rom_data[GB_ROM_SIZE];
        info.ram_size_code = rom_data[GB_RAM_SIZE];

        // Header checksum
        info.header_checksum = rom_data[GB_CHECKSUM];

        // Verify header checksum
        uint8_t sum = 0;
        for (int i = 0x0134; i < 0x014D; i++) {
            sum = sum - rom_data[i] - 1;
        }
        if (sum != info.header_checksum && debug_enabled) {
            printf("ROM: Header checksum mismatch (calc=0x%02X, stored=0x%02X)\n",
                   sum, info.header_checksum);
        }
    }
};

#endif // ROM_LOADER_H
