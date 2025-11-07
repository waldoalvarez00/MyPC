# Verilog/SystemVerilog Floppy Disk Controller Implementations on GitHub

## Comprehensive List of Compatible Chips and Cores

This document catalogs available Verilog/SystemVerilog implementations of floppy disk controllers found on GitHub, organized by chip type and compatibility.

---

## 1. Western Digital WD1793/WD1772 Family

### ✅ WD1793 Implementation (Verilog)

**Repository:** [mvvproject/ReVerSE-U9](https://github.com/mvvproject/ReVerSE-U9/blob/master/u9_vector/src/floppy/wd1793.v)
- **Author:** Viacheslav Slavinsky
- **License:** Modified BSD License
- **Platform:** Vector-06C FPGA replica
- **Language:** Verilog
- **Functionality:**
  - Approximates WD1793 floppy disk controller behavior
  - Supports: Restore, Seek, Step, Read Sector, Write Sector, Read Address
  - Multisector operations when enabled
  - **Limitations:** Track read/write operations NOT supported
  - Acts as command interface to workhorse CPU for actual image file access
- **Interface Signals:** Host I/O, sector buffer memory, CPU communication, IRQ, DRQ
- **Status:** ✅ Working implementation
- **Notes:** Provides basic sector-level operations, not full track-level emulation

**Alternate Repository:** [svofski/vector06cc](https://github.com/svofski/vector06cc/blob/master/src/floppy/wd1793.v)
- Same implementation, different Vector-06C project

### ✅ WD1772 Implementation (VHDL - Not Verilog)

**Repository:** [Torlus/firebee-fpga](https://github.com/Torlus/firebee-fpga/blob/master/FalconIO_SDCard_IDE_CF/WF_FDC1772_IP/wf1772ip_top_soc.vhd)
- **Language:** VHDL (not Verilog, but included for completeness)
- **Platform:** SUSKA ATARI clone project
- **Functionality:** Full implementation of Western Digital WD1772-02 controller
- **Status:** ✅ Complete implementation
- **Notes:** Most feature-complete WD17xx implementation found, but in VHDL

### ⚠️ WD1772 Verilator Testbench

**Repository:** [harbaum/fdc1772-verilator](https://github.com/harbaum/fdc1772-verilator)
- **Purpose:** Verilator simulation environment for FDC1772
- **Platform:** Archimedes FPGA "Archie" core testing
- **Status:** Test environment, not standalone core

---

## 2. Intel 8272 / NEC uPD765 Family (PC Compatible)

### ⚠️ No Pure Verilog Implementation Found

**Status:** No dedicated Verilog core implementation of Intel 8272/NEC uPD765 discovered on GitHub.

**Available Alternatives:**
- **C++ emulation:** MAME `upd765.cpp` - Software emulation only
- **C emulation:** SIMH `i8272.c` - Software emulation only
- **Hardware boards:** Multiple PCB designs using actual chips, not HDL cores

**Closest Match:**
- **ao486** (see below) - Contains floppy controller as part of full 486 SoC

---

## 3. Complete x86 Systems with Integrated Floppy Controllers

### ✅ ao486 - 486 SX Compatible Core

**Repository:** [alfikpl/ao486](https://github.com/alfikpl/ao486)
- **Language:** Verilog
- **Description:** Complete x86 compatible core implementing all features of a 486 SX
- **Floppy Controller:**
  - Integrated floppy controller redirects to SD card driver
  - Resource usage: 1,514 logic cells, 2 M9K memory blocks
  - OSD support for inserting/removing floppy disks
  - NIOS2 controller manages floppy operations
- **Verified Compatible:**
  - MS-DOS 6.22
  - Windows for Workgroups 3.11
  - Windows 95
  - Linux 3.13.1
- **MiSTer Port:** [MiSTer-devel/ao486_MiSTer](https://github.com/MiSTer-devel/ao486_MiSTer)
- **Status:** ✅ Production quality, actively used
- **Source Location:** `rtl/` directory (specific .v files not individually documented)

**Related Project:**
**Repository:** [archlabo/Frix](https://github.com/archlabo/Frix)
- IBM PC Compatible SoC using ao486 modules
- Uses ao486 processor, VGA, PS/2, PIT, RTC, HDD modules
- Floppy controller not explicitly mentioned

---

## 4. Amiga Paula Chip (with Floppy Controller)

### ✅ Amiga Replacement Project - Paula

**Repository:** [nonarkitten/amiga_replacement_project](https://github.com/nonarkitten/amiga_replacement_project)
- **File:** [paula/Paula.v](https://github.com/nonarkitten/amiga_replacement_project/blob/master/paula/Paula.v)
- **Language:** Verilog
- **Description:** Clean Verilog source for Amiga Paula chip
- **Goal:** Perfect compatibility as drop-in replacement for original chip
- **Features:**
  - Disk digital phase locked loop (based on Commodore-Amiga patent #4,780,844)
  - Integrated floppy disk controller functionality
  - Audio subsystem
- **Platform:** OCS (Original Chip Set) implementation
- **Status:** ✅ Active development
- **License:** Open source

### ✅ Minimig-AGA for MiSTer

**Repository:** [MiSTer-devel/Minimig-AGA_MiSTer](https://github.com/MiSTer-devel/Minimig-AGA_MiSTer)
- **Language:** Verilog
- **Description:** Open source re-implementation of Amiga using FPGA
- **Features:**
  - Complete Amiga system including Paula
  - Microcontroller interacts with floppy disk controller in FPGA
  - Supports ADF disk images
- **Status:** ✅ Production quality
- **Documentation:** [How the Minimig Core Works](https://github.com/mist-devel/mist-board/wiki/HowTheMinimigCoreWorks)

### ✅ Amigo - Amiga 1000 in Verilog

**Repository:** [ezrec/Amigo](https://github.com/ezrec/Amigo)
- **Language:** Verilog 2001 RTL
- **Description:** Conversion of Amiga 1000 schematic into Verilog
- **Status:** 🚧 In development
- **Plans:** Wrappers for Minimig's OCS cores (Paula, Agnus, Denise)

---

## 5. Apple Disk Controllers

### ✅ Apple IWM Chip Implementation

**Repository:** [steve-chamberlin/fpga-disk-controller](https://github.com/steve-chamberlin/fpga-disk-controller)
- **Language:** Verilog
- **Description:** FPGA-based disk controller card for Apple II
- **Features:**
  - Full Verilog implementation of Apple IWM chip
  - Verilog replacements for 7400-series logic
  - Liron clone design
- **Platform:** Apple II
- **Status:** ✅ Working implementation
- **Directory:** `lattice/` contains Verilog code

---

## 6. ZX Spectrum Beta Disk Interface

### ✅ ZX Spectrum Beta Disk Controller (WD1793-based)

**Repository:** [MiSTer-devel/ZX-Spectrum_MISTer](https://github.com/MiSTer-devel/ZX-Spectrum_MISTer)
- **Language:** Verilog
- **Description:** ZX Spectrum core with TR-DOS (Beta Disk Interface)
- **Controller:** Based on WD1793
- **Supported Formats:**
  - TRD images (read/write)
  - SCL images (read-only)
- **Source:** Uses Verilog models from Till Harbaum Spectrum core
- **Status:** ✅ Working on MiSTer
- **Notes:** Very common on Russian ZX Spectrum clones

**Related Repository:** [alvaroalea/betadisk-clone](https://github.com/alvaroalea/betadisk-clone)
- Clone of the Beta 128 Disk Interface for ZX Spectrum
- Hardware PCB design

**Related Repository:** [sorgelig/ZX_Spectrum-128K_MIST](https://github.com/sorgelig/ZX_Spectrum-128K_MIST)
- ZX Spectrum 128K for MIST Board
- TR-DOS Beta Disk Interface support
- Native TRD images

**Related Repository:** [mikestir/fpga-spectrum](https://github.com/mikestir/fpga-spectrum)
- Sinclair ZX Spectrum 48k/128k on Altera DE1

---

## 7. Commodore 64 - 1541 Disk Drive

### ✅ C64 with 1541 Controller

**Repository:** [markus-zzz/myc64](https://github.com/markus-zzz/myc64)
- **Language:** Verilog
- **Description:** C64 implementation in Verilog
- **Status:** 🔍 Investigate for 1541 implementation details

**Repository:** [ovalcode/c64fpga](https://github.com/ovalcode/c64fpga)
- **Language:** Verilog/VHDL
- **Platform:** ZYBO Development Board
- **Description:** Commodore 64 implementation
- **Status:** 🔍 Investigate for 1541 implementation details

**Repository:** [MiSTer-devel/C64_MiSTer](https://github.com/MiSTer-devel/C64_MiSTer)
- **Language:** Verilog
- **Based on:** FPGA64 by Peter Wendrich
- **Features:**
  - C1541 implementation by darfpga
  - Supports D64, T64, G64, G81 images
- **Status:** ✅ Working on MiSTer

**Repository:** [MiSTle-Dev/C64Nano](https://github.com/MiSTle-Dev/C64Nano)
- **Language:** Verilog
- **Platform:** Tang Nano FPGA boards
- **Features:** Original C64 core by Peter Wendrich, c1541 by darfpga
- **Status:** ✅ Working

**Reference:** [mist-devel/c16](https://github.com/mist-devel/c16)
- Includes floppy 1541 (read only)
- Source: http://darfpga.blogspot.de
- Status: ✅ Read-only implementation

---

## 8. Hardware Boards Using Real Chips (Not HDL Cores)

These projects use actual floppy controller ICs, not Verilog implementations:

### Hardware Projects (Reference Only)

**skiselev/flock-v2** - [Link](https://github.com/skiselev/flock-v2)
- NEC uPD765 compatible hardware with integrated data separator
- CPLD uses VHDL (not Verilog)
- RC2014/RCBUS compatible

**skiselev/isa-fdc** - [Link](https://github.com/skiselev/isa-fdc)
- Based on Intel 82077AA or National Semiconductor PC8477 FDC IC
- ISA bus floppy disk and serial controller

**skiselev/monster-fdc** - [Link](https://github.com/skiselev/monster-fdc)
- ISA floppy disk controller supporting up to 8 drives
- Uses actual FDC chips

**merlinkv/ZX_2A-2B_FDD_Controller** - [Link](https://github.com/merlinkv/ZX_2A-2B_FDD_Controller)
- Compatible with NEC UPD765 (D765AC-2), Zilog Z0765A08PSC, UMC UM8272A
- Hardware PCB design

---

## Summary Matrix

| Chip Type | Repository | Language | Status | Platform |
|-----------|-----------|----------|--------|----------|
| WD1793 | mvvproject/ReVerSE-U9 | Verilog | ✅ Working | Vector-06C |
| WD1793 | svofski/vector06cc | Verilog | ✅ Working | Vector-06C |
| WD1772 | Torlus/firebee-fpga | VHDL | ✅ Working | Firebee |
| 8272/uPD765 | ❌ Not found | - | ❌ None | - |
| 486 FDC | alfikpl/ao486 | Verilog | ✅ Production | MiSTer/ao486 |
| Paula (Amiga) | nonarkitten/amiga_replacement_project | Verilog | ✅ Active | Amiga OCS |
| Paula (Amiga) | MiSTer-devel/Minimig-AGA_MiSTer | Verilog | ✅ Production | MiSTer |
| Apple IWM | steve-chamberlin/fpga-disk-controller | Verilog | ✅ Working | Apple II |
| WD1793 (Beta) | MiSTer-devel/ZX-Spectrum_MISTer | Verilog | ✅ Working | ZX Spectrum |
| C1541 | MiSTer-devel/C64_MiSTer | Verilog | ✅ Working | C64 |
| C1541 | darfpga (various) | Verilog | ✅ Working | C64 |

---

## Recommendations for PC-Compatible Floppy Controller

### Best Options:

1. **For PC Compatibility:**
   - **ao486** - Use the integrated floppy controller from the ao486 project
   - Most complete PC-compatible solution
   - Production quality, actively maintained
   - Supports standard PC floppy formats

2. **For WD17xx Compatibility:**
   - **WD1793 from Vector-06C** - Sector-level operations
   - **WD1772 VHDL** - Full implementation (requires VHDL support or conversion)

3. **For Reference/Study:**
   - **Amiga Paula** - Well-documented, clean Verilog
   - **Apple IWM** - Complete custom controller implementation

### Missing Implementations:

- **Intel 8272 / NEC uPD765** - No standalone Verilog core found
- Would need to extract from ao486 or implement from scratch
- C/C++ emulations available in MAME/SIMH for reference

---

## License Information

Most implementations use permissive open-source licenses:
- **BSD License:** WD1793 (modified BSD)
- **GPL:** ao486, Minimig cores
- **Open Source:** Amiga Replacement Project

Always verify license compatibility before using in your project.

---

## Additional Resources

### Documentation:
- [How the Minimig Core Works](https://github.com/mist-devel/mist-board/wiki/HowTheMinimigCoreWorks)
- Commodore-Amiga Patent #4,780,844 (Disk PLL design)
- WD1772/WD1793 datasheets (for reference)

### Communities:
- MiSTer FPGA community
- FPGA Arcade forums
- Retro computing FPGA developers

---

**Report Generated:** November 6, 2025
**Research Method:** GitHub web search
**Total Implementations Found:** 10+ Verilog/HDL cores
**PC-Compatible:** 1 (ao486 integrated)
**WD17xx Compatible:** 3 (2 Verilog, 1 VHDL)
