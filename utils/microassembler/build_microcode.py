#!/usr/bin/env python3

import os
import sys

# Import the microassembler script
import uasm

def main():
    # Define the source directory and binary directory
    source_dir = 'microcode'
    binary_dir = '../../Quartus/rtl/CPU'

    # List of microprogram sources
    microprogram_sources = [
        'aaa.us', 'aad.us', 'aas.us', 'adc.us', 'add.us', 'and.us',
        'bound.us', 'daa.us', 'das.us', 'arithmetic.us', 'call.us',
        'comparison.us', 'cmp.us', 'cmps.us', 'div.us', 'enter.us',
        'esc.us', 'extend.us', 'flags.us', 'hlt.us', 'inc.us', 'int.us',
        'io.us', 'jmp.us', 'lds.us', 'lea.us', 'leave.us', 'les.us',
        'lods.us', 'loop.us', 'mov.us', 'movs.us', 'mul.us', 'neg.us',
        'not.us', 'or.us', 'pop.us', 'push.us', 'rcl.us', 'rcr.us',
        'ret.us', 'rol.us', 'ror.us', 'sar.us', 'sbb.us', 'scas.us',
        'shift.us', 'shl.us', 'shr.us', 'stos.us', 'sub.us', 'test.us',
        'xchg.us', 'xlat.us', 'xor.us', 'wait.us', 'microcode.us',
        'debug.us'
    ]

    # Add the directory prefix to each source file
    microprogram_sources = [os.path.join(source_dir, f) for f in microprogram_sources]

    # Define output file paths
    bin_output = os.path.join(binary_dir, 'microcode.bin')
    mif_output = os.path.join(binary_dir, 'microcode.mif')
    verilog_output = os.path.join(binary_dir, 'InstructionDefinitions.sv')
    verilog_types_output = os.path.join(binary_dir, 'MicrocodeTypes.sv')
    cpp_types_output = os.path.join(binary_dir, 'MicrocodeTypes.h')

    # Include directories
    # Add source_dir so #include "arithmetic.us" etc. can find header files
    # Add '.' (current dir) so #include <config.h> can find utils/microassembler/config.h
    include_dirs = ['.', source_dir, binary_dir, os.path.join(binary_dir, '..')]

    print("=" * 70)
    print("Building CPU Microcode")
    print("=" * 70)
    print(f"Source directory: {source_dir}")
    print(f"Output directory: {binary_dir}")
    print(f"Input files: {len(microprogram_sources)} microcode files")
    print("")

    # Run the assembler
    assembler = uasm.MicroAssembler(
        microprogram_sources,
        bin_output,
        mif_output,
        verilog_output,
        verilog_types_output,
        cpp_types_output,
        include_dirs
    )

    try:
        assembler.assemble()
        print("")
        print("=" * 70)
        print("✓ Microcode build successful!")
        print("=" * 70)
        print(f"Generated files:")
        print(f"  - {verilog_output}")
        print(f"  - {verilog_types_output}")
        print(f"  - {bin_output}")
        print(f"  - {mif_output}")
        print("")
        return 0
    except Exception as e:
        print("")
        print("=" * 70)
        print("✗ Microcode build FAILED!")
        print("=" * 70)
        print(f"Error: {e}")
        print("")
        import traceback
        traceback.print_exc()
        return 1

if __name__ == "__main__":
    sys.exit(main())
