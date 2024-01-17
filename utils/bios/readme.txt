# Building the BIOS

You need some linux to build the BIOS because gcc 16 bits is only currently available on Linux. You can use VMware Player that is free, Virtual Box or Hyper-V

I installed Ubuntu 22.04.3 LTS

First install 16bits gcc. In ubuntu or similar console type:

sudo add-apt-repository ppa:tkchia/build-ia16
sudo apt-get update
sudo apt-get install gcc-ia16-elf


later install make:

sudo apt install make

At the BIOS directory type:

make

This will create a folder "output" where bios-mypc will be created


Later you need to process this file (bios-mypc) with the python script to create a .mif file, type:

python make-bios-mif.py bios-mypc bios.mif


drop this .mif file at the root of the Quartus folder and build the project with the new BIOS


# Notes about the BIOS

The BIOS starts at entry.S this is AT&T assembler and creates an environment where the C can kick in


# Dissassembling the BIOS

you can use objdump, is not the best but will give close output of what is in memory:

intel syntax

objdump -D -b binary -m i386 -Maddr16,data16 --adjust-vma=0xc000 -M intel bios-mypc > disasm.txt

at&t syntax

objdump -D -b binary -m i386 -Maddr16,data16 --adjust-vma=0xc000 bios-mypc > disasm.txt



