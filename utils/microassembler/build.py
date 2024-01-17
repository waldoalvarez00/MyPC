#!/usr/bin/env python3

# Copyright Waldo Alvarez, 2023
# https://pipflow.com
#
# This file is part of s80x86.
#
# s80x86 is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# s80x86 is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with s80x86.  If not, see <http://www.gnu.org/licenses/>.


import os
import sys

# Import the microassembler script
import uasm

def main():
	# Define the source directory and binary directory
	source_dir = 'microcode'  # Update with the actual path
	binary_dir = 'outputbin'  # Update with the actual path

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
	'debug.us'  # Add any additional microcode files here
	]


	# Add the directory prefix to each source file
	microprogram_sources = [os.path.join(source_dir, f) for f in microprogram_sources]

	# Define output file paths
	bin_output = os.path.join(binary_dir, 'microcode.bin')
	mif_output = os.path.join(binary_dir, 'microcode.mif')
	verilog_output = os.path.join(binary_dir, 'Microcode.sv')
	verilog_types_output = os.path.join(binary_dir, 'MicrocodeTypes.sv')
	cpp_types_output = os.path.join(binary_dir, 'MicrocodeTypes.h')

	# Include directories (adjust as needed)
	include_dirs = [binary_dir, os.path.join(binary_dir, '..')]

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

	assembler.assemble()

if __name__ == "__main__":
	main()
