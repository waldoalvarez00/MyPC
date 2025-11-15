# MyPC - Complete 80186 + 8087 PC Emulation for MiSTer

This project is a comprehensive port of Jamie Iles' computer to the MiSTer platform, featuring a complete **80186 CPU** with **8087 Floating Point Unit** and full **VGA/MCGA/CGA/EGA** graphics support. It is still under developement. Central to its design is the incorporation of a **microassembler** for both CPU and FPU microcode, significantly enhancing the system's modifiability and maintainability. The project's primary objective is to emulate the architecture and functionality of a traditional PC, emphasizing binary compatibility over cycle-accurate replication.

## Key Features

### **80186 CPU with Microcode Architecture**
The system's architecture is designed around **16-bit buses**, ensuring efficient data transfer and significantly boosting overall performance. The CPU integrates **2-Way Set associative** cache memory with internal Harvard architecture (DCache+ICache) for enhanced processing speed and data access efficiency.

### **8087 Floating Point Unit (FPU) - FULLY IMPLEMENTED (still requires testing)** ✅
The system now includes a **complete IEEE 754-compliant (still needs verification) 8087 FPU** with authentic coprocessor interface:
- **All 8 phases complete**: 165/165 tests passing (100%)
- **Full instruction set**: Arithmetic, transcendental functions (SIN, COS, TAN, ATAN, LOG), BCD operations
- **Authentic architecture**: Dedicated coprocessor ports matching original 8086+8087 design
- **Optimized for MiSTer**: through shared arithmetic units and microcode orchestration
- **Production ready in simulation**: System fits comfortably at 78% FPGA utilization
- See `Quartus/rtl/FPU8087/` for complete implementation details

### **Complete VGA/MCGA/CGA/EGA Graphics Support** ✅
The video subsystem supports **all 15 standard PC video modes** with comprehensive CRTC-based mode detection:
- **CGA Text Modes**: 40×25 and 80×25 in B&W and color (modes 00h-03h)
- **CGA Graphics**: 320×200 4-color, 640×200 2-color (modes 04h-06h)
- **MDA**: 80×25 monochrome text, 720×350 resolution (mode 07h)
- **EGA Graphics**: 320×200 and 640×200 16-color, 640×350 16-color and monochrome (modes 0Dh-10h)
- **VGA Graphics**: 640×480 in 2-color and 16-color (modes 11h-12h)
- **MCGA**: 320×200 256-color Mode 13h
- **Test Coverage**: 15/15 modes passing (100%)
- **Shared Memory Architecture**: SDRAM-based framebuffer shared with CPU for optimal resource utilization

The comprehensive video implementation supports dynamic mode switching with proper CRTC register programming, enabling authentic PC graphics output from text-based DOS applications to colorful VGA games.


![Booting](https://github.com/waldoalvarez00/MyPC/blob/main/img/bootshot.jpg?raw=true)
