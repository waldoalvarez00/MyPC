# BIOS Building Project

This project outlines the steps to build a BIOS using a Linux environment. The primary focus is on using a 16-bit GCC compiler, which is available only on Linux platforms. This guide uses Ubuntu 22.04.3 LTS as the base system.

## Prerequisites

- Linux Environment (Ubuntu 22.04.3 LTS recommended)
- Virtualization Tool (VMware Player, Virtual Box, or Hyper-V)

## Installation

### Install 16-bit GCC

To install the 16-bit version of GCC, open your terminal and execute the following commands:

```bash
sudo add-apt-repository ppa:tkchia/build-ia16
sudo apt-get update
sudo apt-get install gcc-ia16-elf
```

### Install Make

You'll also need 'make' for building the BIOS. Install it by typing:

```bash
sudo apt install make
```

At the BIOS directory type:

```bash
make
```

This command creates an "output" folder where bios-mypc will be generated.


## Post-Build Processing

To convert the bios-mypc file to a .mif file, use the provided Python script:

```bash
python make-bios-mif.py bios-mypc bios.mif
```

Place the resulting bios.mif file at the root of your Quartus folder and rebuild the project with the new BIOS.

# Notes about the BIOS

The BIOS starts at entry.S this is AT&T assembler and creates an environment where the C can kick in

# Disassembling the BIOS

you can use objdump, is not the best but will give close output of what is in memory:

intel syntax:

```bash
objdump -D -b binary -m i386 -Maddr16,data16 --adjust-vma=0xc000 -M intel bios-mypc > disasm.txt
```

at&t syntax:

```bash
objdump -D -b binary -m i386 -Maddr16,data16 --adjust-vma=0xc000 bios-mypc > disasm.txt
```
