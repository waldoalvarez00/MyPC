#include <stdio.h>

int main() {
    FILE* f = fopen("dmg_boot.bin", "rb");
    if (!f) f = fopen("../gameboy_core/BootROMs/bin/dmg_boot.bin", "rb");
    if (!f) {
        printf("Could not load boot ROM\n");
        return 1;
    }

    unsigned char boot_rom[256];
    fread(boot_rom, 1, 256, f);
    fclose(f);

    printf("=== GameBoy Boot ROM Disassembly (First 32 bytes) ===\n\n");

    printf("Address  Hex      Instruction\n");
    printf("-------  -------  -----------\n");

    for (int i = 0; i < 32; ) {
        printf("$%04X    %02X       ", i, boot_rom[i]);

        switch (boot_rom[i]) {
            case 0x31:  // LD SP, nn
                printf("LD SP, $%02X%02X\n", boot_rom[i+2], boot_rom[i+1]);
                i += 3;
                break;
            case 0x21:  // LD HL, nn
                printf("LD HL, $%02X%02X\n", boot_rom[i+2], boot_rom[i+1]);
                i += 3;
                break;
            case 0x22:  // LD (HL+), A
                printf("LD (HL+), A\n");
                i += 1;
                break;
            case 0xCB:  // CB prefix
                printf("CB %02X    ", boot_rom[i+1]);
                i += 2;
                int bit = (boot_rom[i-1] >> 3) & 7;
                int reg = boot_rom[i-1] & 7;
                const char* regs[] = {"B", "C", "D", "E", "H", "L", "(HL)", "A"};
                printf("BIT %d, %s\n", bit, regs[reg]);
                break;
            case 0x28:  // JR Z, n
                printf("28 %02X    ", boot_rom[i+1]);
                signed char offset = (signed char)boot_rom[i+1];
                int target = i + 2 + offset;
                printf("JR Z, $%04X (offset %+d)\n", target, offset);
                i += 2;
                break;
            case 0x3E:  // LD A, n
                printf("3E %02X    LD A, $%02X\n", boot_rom[i+1], boot_rom[i+1]);
                i += 2;
                break;
            case 0xE0:  // LD (FF00+n), A
                printf("E0 %02X    LD ($FF%02X), A\n", boot_rom[i+1], boot_rom[i+1]);
                i += 2;
                break;
            case 0xFC:  // illegal/unknown
                printf("       ???\n");
                i += 1;
                break;
            case 0xF0:  // LD A, (FF00+n)
                printf("F0 %02X    LD A, ($FF%02X)\n", boot_rom[i+1], boot_rom[i+1]);
                i += 2;
                break;
            case 0xFE:  // CP n
                printf("FE %02X    CP $%02X\n", boot_rom[i+1], boot_rom[i+1]);
                i += 2;
                break;
            case 0xFF:  // RST 38
                printf("       RST $38\n");
                i += 1;
                break;
            default:
                printf("       ??? (unknown opcode)\n");
                i += 1;
        }
    }

    printf("\n");
    return 0;
}
