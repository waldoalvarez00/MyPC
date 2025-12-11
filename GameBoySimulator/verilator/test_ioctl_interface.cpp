#include <verilated.h>
#include "Vtop.h"
#include "Vtop___024root.h"
#include "gb_test_common.h"
#include <stdio.h>

int main() {
    Vtop* dut = new Vtop;
    MisterSDRAMModel* sdram = new MisterSDRAMModel(8*1024*1024);
    sdram->cas_latency = 2;  // Realistic CAS latency

    printf("=== Verification 3: ioctl Download Interface ===\n\n");

    // Initialize
    dut->reset = 1;
    dut->inputs = 0xFF;
    dut->ioctl_download = 0;
    dut->boot_download = 0;
    run_cycles_with_sdram(dut, sdram, 50);
    dut->reset = 0;

    printf("Step 1: Write test pattern to cart ROM via ioctl...\n");

    dut->ioctl_download = 1;
    dut->ioctl_index = 0;

    // Write test pattern: AA BB CC DD at addresses $0104-$0107
    printf("  Writing $AABB to cart[$0104]\n");
    dut->ioctl_addr = 0x0104 >> 1;  // Word address
    dut->ioctl_dout = 0xBBAA;        // Little endian: $AA at $0104, $BB at $0105
    dut->ioctl_wr = 1;
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    tick_with_sdram(dut, sdram);

    printf("  Writing $DDCC to cart[$0106]\n");
    dut->ioctl_addr = 0x0106 >> 1;
    dut->ioctl_dout = 0xDDCC;
    dut->ioctl_wr = 1;
    tick_with_sdram(dut, sdram);
    dut->ioctl_wr = 0;
    tick_with_sdram(dut, sdram);

    dut->ioctl_download = 0;
    printf("✓ Test pattern written\n\n");

    // Wait for SDRAM operations to complete
    run_cycles_with_sdram(dut, sdram, 1000);

    printf("Step 2: Try to read back from SDRAM model directly...\n");

    // The SDRAM model should have the data at the cart ROM offset
    // Cart ROM typically maps to SDRAM starting at some offset
    // Let's check if SDRAM has our data
    printf("  (Note: SDRAM model internal state not directly accessible)\n");
    printf("  Will verify by CPU read in next step\n\n");

    printf("Step 3: Load boot ROM and have CPU read from cart ROM...\n");

    // Load minimal boot ROM that just reads from $0104
    uint8_t test_boot_rom[256];
    memset(test_boot_rom, 0, 256);

    // Simple program to read and write cart ROM data
    int idx = 0;
    test_boot_rom[idx++] = 0x31;  // LD SP, $FFFE
    test_boot_rom[idx++] = 0xFE;
    test_boot_rom[idx++] = 0xFF;

    test_boot_rom[idx++] = 0x21;  // LD HL, $0104 (cart ROM address)
    test_boot_rom[idx++] = 0x04;
    test_boot_rom[idx++] = 0x01;

    test_boot_rom[idx++] = 0x2A;  // LD A, (HL+)  - Read from $0104
    test_boot_rom[idx++] = 0x2A;  // LD A, (HL+)  - Read from $0105
    test_boot_rom[idx++] = 0x2A;  // LD A, (HL+)  - Read from $0106
    test_boot_rom[idx++] = 0x2A;  // LD A, (HL+)  - Read from $0107

    test_boot_rom[idx++] = 0x76;  // HALT

    // Disable boot ROM by writing to $FF50
    test_boot_rom[0xFE] = 0x3E;  // LD A, $01
    test_boot_rom[0xFF] = 0x01;

    dut->reset = 1;
    run_cycles_with_sdram(dut, sdram, 50);

    dut->boot_download = 1;
    for (int i = 0; i < 256; i += 2) {
        dut->boot_addr = i;
        dut->boot_data = test_boot_rom[i] | (test_boot_rom[i+1] << 8);
        dut->boot_wr = 1;
        tick_with_sdram(dut, sdram);
        dut->boot_wr = 0;
        tick_with_sdram(dut, sdram);
    }
    dut->boot_download = 0;

    run_cycles_with_sdram(dut, sdram, 100);
    dut->reset = 0;

    printf("Monitoring CPU reads from $0104-$0107...\n");

    uint8_t read_data[4] = {0xFF, 0xFF, 0xFF, 0xFF};
    int read_count = 0;

    for (int i = 0; i < 5000; i++) {
        uint16_t addr = dut->dbg_cpu_addr;
        uint8_t rd_n = dut->dbg_cpu_rd_n;
        uint8_t data_in = dut->dbg_cpu_di;
        uint16_t pc = dut->dbg_cpu_pc;
        bool boot_enabled = dut->dbg_boot_rom_enabled;

        if (rd_n == 0 && addr >= 0x0104 && addr <= 0x0107 && boot_enabled) {
            int idx = addr - 0x0104;
            if (read_data[idx] == 0xFF) {  // First read of this address
                read_data[idx] = data_in;
                read_count++;
                printf("  [%6d] PC=$%04X read cart[$%04X]: data=$%02X\n",
                       i, pc, addr, data_in);
            }
        }

        tick_with_sdram(dut, sdram);

        if (read_count >= 4) break;
    }

    printf("\n--- Results ---\n");
    printf("Expected pattern: AA BB CC DD\n");
    printf("Actual read:      %02X %02X %02X %02X\n",
           read_data[0], read_data[1], read_data[2], read_data[3]);

    bool pass = (read_data[0] == 0xAA && read_data[1] == 0xBB &&
                 read_data[2] == 0xCC && read_data[3] == 0xDD);

    if (pass) {
        printf("\n✅ PASS: ioctl interface working correctly!\n");
    } else {
        printf("\n❌ FAIL: ioctl interface not providing correct data!\n");
        printf("   Possible causes:\n");
        printf("   - ioctl_download not writing to SDRAM\n");
        printf("   - SDRAM address mapping issue\n");
        printf("   - Cart ROM read path not accessing SDRAM\n");
        printf("   - Boot ROM shadow interfering with cart reads\n");
    }

    delete sdram;
    delete dut;
    return pass ? 0 : 1;
}
