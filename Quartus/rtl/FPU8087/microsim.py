#!/usr/bin/env python3
"""
FPU Microsequencer Simulator

This simulator executes microcode programs for the Intel 8087 FPU microsequencer.
It models the microsequencer state machine, FPU registers, and all micro-operations.

Usage:
  python microsim.py microcode.hex
  python microsim.py microcode.hex --verbose
  python microsim.py microcode.hex --test
"""

import sys
import argparse
import struct
from typing import List, Dict, Optional, Tuple
from dataclasses import dataclass
from enum import IntEnum


# ============================================================================
# Opcode and Micro-operation Definitions (same as assembler)
# ============================================================================

class Opcode(IntEnum):
    """Main instruction opcodes"""
    NOP   = 0x0
    EXEC  = 0x1
    JUMP  = 0x2
    CALL  = 0x3
    RET   = 0x4
    HALT  = 0xF


class MicroOp(IntEnum):
    """Micro-operations (used when opcode == EXEC)"""
    LOAD           = 0x1
    STORE          = 0x2
    SET_CONST      = 0x3
    ACCESS_CONST   = 0x4
    ADD_SUB        = 0x5  # immediate[0]: 0=add, 1=sub
    MUL            = 0x6  # Multiply temp_fp_a * temp_fp_b
    DIV            = 0x7  # Divide temp_fp_a / temp_fp_b
    SHIFT          = 0x8  # immediate[0]: 0=left, 1=right; immediate[7:1]=amount
    LOOP_INIT      = 0x9
    LOOP_DEC       = 0xA
    ABS            = 0xB
    NORMALIZE      = 0xC
    COMPARE        = 0xD  # Compare temp_fp_a with temp_fp_b, set flags
    REG_OPS        = 0xE  # immediate: 0=READ_STATUS, 1=READ_CONTROL, 2=READ_TAG, 3=WRITE_STATUS
    ROUND          = 0xF


# ============================================================================
# FPU Extended Precision Float (80-bit) Helper
# ============================================================================

class ExtendedFloat:
    """Represents an 80-bit extended precision floating point number"""

    def __init__(self, value: int = 0):
        """Initialize from 80-bit integer representation"""
        self.bits = value & 0xFFFFFFFFFFFFFFFFFFFF

    @property
    def sign(self) -> int:
        """Get sign bit (bit 79)"""
        return (self.bits >> 79) & 1

    @property
    def exponent(self) -> int:
        """Get exponent (bits 78:64)"""
        return (self.bits >> 64) & 0x7FFF

    @property
    def mantissa(self) -> int:
        """Get mantissa (bits 63:0)"""
        return self.bits & 0xFFFFFFFFFFFFFFFF

    def to_float(self) -> float:
        """Convert to Python float (approximate)"""
        if self.bits == 0:
            return 0.0

        # Extract components
        sign = -1.0 if self.sign else 1.0
        exp = self.exponent - 0x3FFF  # Remove bias
        mant = self.mantissa / (2**63)  # Normalize

        if self.exponent == 0:  # Denormalized
            return sign * mant * (2 ** (exp + 1))
        elif self.exponent == 0x7FFF:  # Infinity or NaN
            return float('inf') * sign if self.mantissa == 0 else float('nan')
        else:  # Normalized
            return sign * mant * (2 ** exp)

    @classmethod
    def from_float(cls, value: float) -> 'ExtendedFloat':
        """Create from Python float (approximate)"""
        if value == 0.0:
            return cls(0)

        sign = 1 if value < 0 else 0
        value = abs(value)

        # Get exponent and mantissa
        import math
        if math.isinf(value):
            return cls((sign << 79) | (0x7FFF << 64))
        if math.isnan(value):
            return cls((sign << 79) | (0x7FFF << 64) | 1)

        exp = math.floor(math.log2(value))
        mant = int((value / (2 ** exp)) * (2 ** 63))

        exp_biased = (exp + 0x3FFF) & 0x7FFF

        bits = (sign << 79) | (exp_biased << 64) | (mant & 0xFFFFFFFFFFFFFFFF)
        return cls(bits)

    def __repr__(self):
        return f"ExtFloat(0x{self.bits:020X} ≈ {self.to_float()})"


# ============================================================================
# FPU State
# ============================================================================

@dataclass
class FPUState:
    """Complete FPU state"""
    # Stack registers (8 x 80-bit)
    stack: List[ExtendedFloat]

    # Control and status registers
    status_word: int = 0
    control_word: int = 0x037F  # Default 8087 value
    tag_word: int = 0xFFFF  # All empty

    # Temporary registers
    temp_reg: int = 0  # 64-bit general purpose
    temp_fp: ExtendedFloat = None  # 80-bit FP
    temp_fp_a: ExtendedFloat = None  # Operand A
    temp_fp_b: ExtendedFloat = None  # Operand B

    # Math constant index
    math_const_index: int = 0

    # Loop register
    loop_reg: int = 0

    def __init__(self):
        self.stack = [ExtendedFloat(0) for _ in range(8)]
        self.temp_fp = ExtendedFloat(0)
        self.temp_fp_a = ExtendedFloat(0)
        self.temp_fp_b = ExtendedFloat(0)

    @property
    def stack_top(self) -> int:
        """Get stack top pointer from status word"""
        return (self.status_word >> 11) & 0x7

    def set_stack_top(self, value: int):
        """Set stack top pointer in status word"""
        self.status_word = (self.status_word & ~(0x7 << 11)) | ((value & 0x7) << 11)


# ============================================================================
# Microsequencer Simulator
# ============================================================================

class MicrosequencerSimulator:
    """Simulates the FPU microsequencer"""

    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.microcode_rom: List[int] = [0] * 4096
        self.fpu_state = FPUState()

        # Microsequencer state
        self.pc = 0
        self.call_stack: List[int] = []
        self.halted = False
        self.instruction_count = 0
        self.max_instructions = 10000  # Safety limit

        # Math constants ROM (simplified)
        self.math_constants = self._init_math_constants()

        # CPU bus interface
        self.cpu_data_in = 0
        self.cpu_data_out = 0

    def _init_math_constants(self) -> List[ExtendedFloat]:
        """Initialize mathematical constants"""
        import math
        constants = [ExtendedFloat(0)] * 64  # Expanded to 64 entries

        # Common constants (indices 0-9)
        constants[0] = ExtendedFloat.from_float(math.pi)       # π
        constants[1] = ExtendedFloat.from_float(math.e)        # e
        constants[2] = ExtendedFloat.from_float(0.0)           # 0.0
        constants[3] = ExtendedFloat.from_float(1.0)           # 1.0
        constants[4] = ExtendedFloat.from_float(2.0)           # 2.0
        constants[5] = ExtendedFloat.from_float(3.0)           # 3.0
        constants[6] = ExtendedFloat.from_float(math.pi/4)     # π/4
        constants[7] = ExtendedFloat.from_float(math.log(2))   # ln(2) ≈ 0.693147
        constants[8] = ExtendedFloat.from_float(0.5)           # 0.5
        constants[9] = ExtendedFloat.from_float(0.6072529350088812)  # K (CORDIC scaling factor)

        # Additional useful constants (indices 10-15)
        constants[10] = ExtendedFloat.from_float(1.0 / math.log(2))  # 1/ln(2) ≈ 1.442695 (for log2)
        constants[11] = ExtendedFloat.from_float(math.log10(2))      # log10(2) ≈ 0.301030
        constants[12] = ExtendedFloat.from_float(1.0 / 6.0)          # 1/6 (for Taylor series)
        constants[13] = ExtendedFloat.from_float(1.0 / 24.0)         # 1/24 (for Taylor series)
        constants[14] = ExtendedFloat.from_float(1.0 / 120.0)        # 1/120 (for Taylor series)
        constants[15] = ExtendedFloat.from_float(1.0 / 720.0)        # 1/720 (for Taylor series)

        # Arctangent table for CORDIC (atan(2^-i) for i=0 to 15) (indices 16-31)
        for i in range(16):
            constants[16 + i] = ExtendedFloat.from_float(math.atan(2.0 ** (-i)))

        # Extended arctangent table (indices 32-47) for higher precision
        for i in range(16, 32):
            constants[32 + (i - 16)] = ExtendedFloat.from_float(math.atan(2.0 ** (-i)))

        # Polynomial coefficients and other constants (indices 48-63)
        # These can be used for various approximations
        constants[48] = ExtendedFloat.from_float(math.sqrt(2))       # √2 ≈ 1.414214
        constants[49] = ExtendedFloat.from_float(1.0 / math.sqrt(2)) # 1/√2 ≈ 0.707107
        constants[50] = ExtendedFloat.from_float(math.pi / 2)        # π/2
        constants[51] = ExtendedFloat.from_float(2.0 * math.pi)      # 2π
        constants[52] = ExtendedFloat.from_float(math.log(10))       # ln(10) ≈ 2.302585
        constants[53] = ExtendedFloat.from_float(1.0 / 3.0)          # 1/3
        constants[54] = ExtendedFloat.from_float(1.0 / 5.0)          # 1/5
        constants[55] = ExtendedFloat.from_float(1.0 / 7.0)          # 1/7

        return constants

    def load_hex_file(self, filename: str):
        """Load microcode from hex file"""
        try:
            with open(filename, 'r') as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith('#'):
                        continue

                    # Parse line: "ADDR: VALUE" or just "VALUE"
                    if ':' in line:
                        addr_str, value_str = line.split(':', 1)
                        addr = int(addr_str.strip(), 16)
                        value = int(value_str.strip(), 16)
                    else:
                        # Sequential loading
                        addr = len([x for x in self.microcode_rom if x != 0])
                        value = int(line.strip(), 16)

                    if 0 <= addr < len(self.microcode_rom):
                        self.microcode_rom[addr] = value

            if self.verbose:
                count = sum(1 for x in self.microcode_rom if x != 0)
                print(f"Loaded {count} microinstructions from {filename}")

        except Exception as e:
            print(f"Error loading {filename}: {e}", file=sys.stderr)
            raise

    def decode_instruction(self, instr: int) -> Tuple[int, int, int, int]:
        """Decode a 32-bit microinstruction"""
        opcode = (instr >> 28) & 0xF
        micro_op = (instr >> 24) & 0xF
        immediate = (instr >> 16) & 0xFF
        next_addr = instr & 0xFFFF
        return opcode, micro_op, immediate, next_addr

    def execute_instruction(self, instr: int) -> bool:
        """Execute a single microinstruction. Returns True if should continue."""
        opcode, micro_op, immediate, next_addr = self.decode_instruction(instr)

        if self.verbose:
            print(f"PC={self.pc:04X}: Instr={instr:08X} Op={opcode:X} MicroOp={micro_op:X} Imm={immediate:02X} Next={next_addr:04X}")

        # Execute based on opcode
        if opcode == Opcode.NOP:
            self.pc = next_addr if next_addr != 0 else self.pc + 1

        elif opcode == Opcode.HALT:
            if self.verbose:
                print("HALT: Microprogram complete")
            self.halted = True
            return False

        elif opcode == Opcode.JUMP:
            if self.verbose:
                print(f"  JUMP to {next_addr:04X}")
            self.pc = next_addr

        elif opcode == Opcode.CALL:
            if self.verbose:
                print(f"  CALL {next_addr:04X} (return addr={self.pc + 1:04X})")
            self.call_stack.append(self.pc + 1)
            self.pc = next_addr

        elif opcode == Opcode.RET:
            if self.call_stack:
                ret_addr = self.call_stack.pop()
                if self.verbose:
                    print(f"  RET to {ret_addr:04X}")
                self.pc = ret_addr
            else:
                if self.verbose:
                    print("  RET: Call stack empty!")
                self.pc = 0

        elif opcode == Opcode.EXEC:
            self._execute_micro_op(micro_op, immediate, next_addr)

        else:
            if self.verbose:
                print(f"  Unknown opcode: {opcode}")
            self.pc = next_addr if next_addr != 0 else self.pc + 1

        return True

    def _execute_micro_op(self, micro_op: int, immediate: int, next_addr: int):
        """Execute a micro-operation"""

        if micro_op == MicroOp.LOAD:
            # Load from CPU bus into temp_reg
            self.fpu_state.temp_reg = self.cpu_data_in
            if self.verbose:
                print(f"  LOAD: temp_reg = 0x{self.cpu_data_in:016X}")

        elif micro_op == MicroOp.STORE:
            # Store temp_reg to CPU bus
            self.cpu_data_out = self.fpu_state.temp_reg
            if self.verbose:
                print(f"  STORE: cpu_data_out = 0x{self.cpu_data_out:016X}")

        elif micro_op == MicroOp.SET_CONST:
            # Set math constant index
            self.fpu_state.math_const_index = immediate & 0x1F
            if self.verbose:
                print(f"  SET_CONST: index = {self.fpu_state.math_const_index}")

        elif micro_op == MicroOp.ACCESS_CONST:
            # Access math constant
            idx = self.fpu_state.math_const_index
            self.fpu_state.temp_fp = self.math_constants[idx]
            if self.verbose:
                print(f"  ACCESS_CONST: temp_fp = {self.fpu_state.temp_fp}")

        elif micro_op == MicroOp.ADD_SUB:
            # Add or subtract (immediate[0] = 0:add, 1:sub)
            is_sub = immediate & 1
            a_val = self.fpu_state.temp_fp_a.to_float()
            b_val = self.fpu_state.temp_fp_b.to_float()

            if is_sub:
                result = a_val - b_val
                if self.verbose:
                    print(f"  SUB: {a_val} - {b_val} = {result}")
            else:
                result = a_val + b_val
                if self.verbose:
                    print(f"  ADD: {a_val} + {b_val} = {result}")

            self.fpu_state.temp_fp = ExtendedFloat.from_float(result)

        elif micro_op == MicroOp.MUL:
            # Multiply temp_fp_a * temp_fp_b
            a_val = self.fpu_state.temp_fp_a.to_float()
            b_val = self.fpu_state.temp_fp_b.to_float()
            result = a_val * b_val
            self.fpu_state.temp_fp = ExtendedFloat.from_float(result)
            if self.verbose:
                print(f"  MUL: {a_val} * {b_val} = {result}")

        elif micro_op == MicroOp.DIV:
            # Divide temp_fp_a / temp_fp_b
            a_val = self.fpu_state.temp_fp_a.to_float()
            b_val = self.fpu_state.temp_fp_b.to_float()
            if b_val == 0:
                result = float('inf') if a_val >= 0 else float('-inf')
            else:
                result = a_val / b_val
            self.fpu_state.temp_fp = ExtendedFloat.from_float(result)
            if self.verbose:
                print(f"  DIV: {a_val} / {b_val} = {result}")

        elif micro_op == MicroOp.SHIFT:
            # Shift operation (left or right)
            direction = immediate & 1  # 0=left, 1=right
            shift_amount = (immediate >> 1) & 0x7F
            if direction == 0:
                # Left shift
                self.fpu_state.temp_reg = (self.fpu_state.temp_reg << shift_amount) & 0xFFFFFFFFFFFFFFFF
                if self.verbose:
                    print(f"  SHIFT_LEFT: {shift_amount} bits")
            else:
                # Right shift
                self.fpu_state.temp_reg = self.fpu_state.temp_reg >> shift_amount
                if self.verbose:
                    print(f"  SHIFT_RIGHT: {shift_amount} bits")

        elif micro_op == MicroOp.LOOP_INIT:
            # Initialize loop counter
            self.fpu_state.loop_reg = immediate
            if self.verbose:
                print(f"  LOOP_INIT: count = {immediate}")

        elif micro_op == MicroOp.LOOP_DEC:
            # Decrement loop counter and jump if not zero
            if self.fpu_state.loop_reg > 0:
                self.fpu_state.loop_reg -= 1
                if self.verbose:
                    print(f"  LOOP_DEC: count = {self.fpu_state.loop_reg}, jumping to {next_addr:04X}")
                self.pc = next_addr
                return  # Don't increment PC at end
            else:
                if self.verbose:
                    print(f"  LOOP_DEC: count = 0, continuing")
                self.pc = self.pc + 1
                return

        elif micro_op == MicroOp.ABS:
            # Absolute value
            val = self.fpu_state.temp_fp.to_float()
            result = abs(val)
            self.fpu_state.temp_fp = ExtendedFloat.from_float(result)
            if self.verbose:
                print(f"  ABS: |{val}| = {result}")

        elif micro_op == MicroOp.ROUND:
            # Round (simplified - just use Python rounding)
            val = self.fpu_state.temp_fp.to_float()
            result = round(val)
            self.fpu_state.temp_fp = ExtendedFloat.from_float(result)
            if self.verbose:
                print(f"  ROUND: round({val}) = {result}")

        elif micro_op == MicroOp.NORMALIZE:
            # Normalize (simplified - already normalized in conversion)
            if self.verbose:
                print(f"  NORMALIZE: {self.fpu_state.temp_fp}")

        elif micro_op == MicroOp.COMPARE:
            # Compare temp_fp_a with temp_fp_b and set flags
            a_val = self.fpu_state.temp_fp_a.to_float()
            b_val = self.fpu_state.temp_fp_b.to_float()

            # Set condition codes in status word (bits 14, 10, 9, 8 = C3, C2, C1, C0)
            # C3 C2 C1 C0
            #  0  0  0  0 : a > b
            #  0  0  0  1 : a < b
            #  1  0  0  0 : a == b
            #  1  1  1  1 : unordered (NaN)
            if a_val > b_val:
                cc = 0b0000
            elif a_val < b_val:
                cc = 0b0001
            else:  # a_val == b_val
                cc = 0b1000

            # Update status word with condition codes
            # C3=bit 14, C2=bit 10, C1=bit 9, C0=bit 8
            self.fpu_state.status_word = (self.fpu_state.status_word & 0x3CFF) | \
                                        ((cc & 0x1) << 8) | \
                                        ((cc & 0x2) << 8) | \
                                        ((cc & 0x4) << 8) | \
                                        ((cc & 0x8) << 11)

            if self.verbose:
                print(f"  COMPARE: {a_val} vs {b_val}, flags={cc:04b}")

        elif micro_op == MicroOp.REG_OPS:
            # Consolidated register operations
            reg_op = immediate & 0xF

            if reg_op == 0:  # READ_STATUS
                self.fpu_state.temp_reg = self.fpu_state.status_word & 0xFFFF
                if self.verbose:
                    print(f"  READ_STATUS: 0x{self.fpu_state.status_word:04X}")

            elif reg_op == 1:  # READ_CONTROL
                self.fpu_state.temp_reg = self.fpu_state.control_word & 0xFFFF
                if self.verbose:
                    print(f"  READ_CONTROL: 0x{self.fpu_state.control_word:04X}")

            elif reg_op == 2:  # READ_TAG
                self.fpu_state.temp_reg = self.fpu_state.tag_word & 0xFFFF
                if self.verbose:
                    print(f"  READ_TAG: 0x{self.fpu_state.tag_word:04X}")

            elif reg_op == 3:  # WRITE_STATUS
                self.fpu_state.status_word = self.fpu_state.temp_reg & 0xFFFF
                if self.verbose:
                    print(f"  WRITE_STATUS: 0x{self.fpu_state.status_word:04X}")

        else:
            if self.verbose:
                print(f"  Unknown micro-op: {micro_op}")

        # Default: advance to next address
        self.pc = next_addr

    def run(self, start_addr: int = 0) -> bool:
        """Run microcode starting at given address"""
        self.pc = start_addr
        self.halted = False
        self.instruction_count = 0

        if self.verbose:
            print(f"\n{'='*60}")
            print(f"Starting execution at address 0x{start_addr:04X}")
            print(f"{'='*60}\n")

        while not self.halted and self.instruction_count < self.max_instructions:
            if self.pc >= len(self.microcode_rom):
                if self.verbose:
                    print(f"PC out of range: {self.pc:04X}")
                break

            instr = self.microcode_rom[self.pc]
            if instr == 0:
                if self.verbose:
                    print(f"Encountered zero instruction at {self.pc:04X}")
                break

            if not self.execute_instruction(instr):
                break

            self.instruction_count += 1

        if self.verbose:
            print(f"\n{'='*60}")
            print(f"Execution complete: {self.instruction_count} instructions")
            print(f"{'='*60}\n")

        return self.halted

    def print_state(self):
        """Print current FPU state"""
        print("\n=== FPU State ===")
        print(f"Status Word:  0x{self.fpu_state.status_word:04X}")
        print(f"Control Word: 0x{self.fpu_state.control_word:04X}")
        print(f"Tag Word:     0x{self.fpu_state.tag_word:04X}")
        print(f"Temp Reg:     0x{self.fpu_state.temp_reg:016X}")
        print(f"Temp FP:      {self.fpu_state.temp_fp}")
        print(f"Loop Reg:     {self.fpu_state.loop_reg}")
        print(f"CPU Out:      0x{self.cpu_data_out:016X}")
        print()


# ============================================================================
# Test Framework
# ============================================================================

class MicrocodeTest:
    """Test case for microcode execution"""

    def __init__(self, name: str, hex_file: str):
        self.name = name
        self.hex_file = hex_file
        self.setup_fn = None
        self.verify_fn = None

    def setup(self, fn):
        """Decorator for setup function"""
        self.setup_fn = fn
        return fn

    def verify(self, fn):
        """Decorator for verification function"""
        self.verify_fn = fn
        return fn

    def run(self, verbose: bool = False) -> bool:
        """Run the test"""
        print(f"\n{'='*60}")
        print(f"Test: {self.name}")
        print(f"{'='*60}")

        sim = MicrosequencerSimulator(verbose=verbose)

        # Setup
        if self.setup_fn:
            self.setup_fn(sim)

        # Load and run
        sim.load_hex_file(self.hex_file)
        success = sim.run()

        # Print state
        if verbose:
            sim.print_state()

        # Verify
        if self.verify_fn:
            try:
                self.verify_fn(sim)
                print(f"✓ PASS: {self.name}")
                return True
            except AssertionError as e:
                print(f"✗ FAIL: {self.name}")
                print(f"  {e}")
                return False
        else:
            if success:
                print(f"✓ PASS: {self.name} (halted normally)")
                return True
            else:
                print(f"✗ FAIL: {self.name} (did not halt)")
                return False


# ============================================================================
# Main Program
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description='FPU Microsequencer Simulator'
    )
    parser.add_argument('hexfile', nargs='?', help='Microcode hex file to execute')
    parser.add_argument('-v', '--verbose', action='store_true',
                       help='Verbose execution trace')
    parser.add_argument('-t', '--test', action='store_true',
                       help='Run test suite')
    parser.add_argument('-s', '--start', type=lambda x: int(x, 0), default=0,
                       help='Start address (default: 0)')

    args = parser.parse_args()

    if args.test:
        # Run test suite
        from test_microcode import run_all_tests
        success = run_all_tests(verbose=args.verbose)
        return 0 if success else 1

    if not args.hexfile:
        parser.print_help()
        return 1

    # Run single program
    sim = MicrosequencerSimulator(verbose=args.verbose)
    sim.load_hex_file(args.hexfile)
    success = sim.run(start_addr=args.start)

    sim.print_state()

    return 0 if success else 1


if __name__ == '__main__':
    sys.exit(main())
