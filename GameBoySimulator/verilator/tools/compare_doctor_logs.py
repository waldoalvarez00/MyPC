#!/usr/bin/env python3
"""
compare_doctor_logs.py - Compare gameboy-doctor log files

Compares a simulator log against a reference trace and reports
the exact instruction where divergence occurs.

Usage:
    python3 compare_doctor_logs.py <reference_log> <test_log>
"""

import sys
import re
from typing import Dict, Tuple, Optional

def parse_log_line(line: str) -> Optional[Dict[str, str]]:
    """
    Parse a gameboy-doctor log line into a dictionary.
    Format: A:XX F:XX B:XX C:XX D:XX E:XX H:XX L:XX SP:XXXX PC:XXXX PCMEM:XX,XX,XX,XX
    """
    line = line.strip()
    if not line or line.startswith('#'):
        return None

    # Regular expression to match the log format
    pattern = r'A:([0-9A-F]{2})\s+F:([0-9A-F]{2})\s+B:([0-9A-F]{2})\s+C:([0-9A-F]{2})\s+D:([0-9A-F]{2})\s+E:([0-9A-F]{2})\s+H:([0-9A-F]{2})\s+L:([0-9A-F]{2})\s+SP:([0-9A-F]{4})\s+PC:([0-9A-F]{4})\s+PCMEM:([0-9A-F]{2}),([0-9A-F]{2}),([0-9A-F]{2}),([0-9A-F]{2})'

    match = re.match(pattern, line)
    if not match:
        return None

    return {
        'A': match.group(1),
        'F': match.group(2),
        'B': match.group(3),
        'C': match.group(4),
        'D': match.group(5),
        'E': match.group(6),
        'H': match.group(7),
        'L': match.group(8),
        'SP': match.group(9),
        'PC': match.group(10),
        'PCMEM0': match.group(11),
        'PCMEM1': match.group(12),
        'PCMEM2': match.group(13),
        'PCMEM3': match.group(14),
    }

def format_state(state: Dict[str, str]) -> str:
    """Format state dictionary back to log line format."""
    return f"A:{state['A']} F:{state['F']} B:{state['B']} C:{state['C']} D:{state['D']} E:{state['E']} H:{state['H']} L:{state['L']} SP:{state['SP']} PC:{state['PC']} PCMEM:{state['PCMEM0']},{state['PCMEM1']},{state['PCMEM2']},{state['PCMEM3']}"

def compare_logs(reference_path: str, test_path: str) -> Tuple[bool, int, Optional[Dict], Optional[Dict]]:
    """
    Compare two log files.
    Returns: (match, line_number, ref_state, test_state)
    """
    try:
        with open(reference_path, 'r') as ref_f, open(test_path, 'r') as test_f:
            line_num = 0
            ref_line_num = 0
            test_line_num = 0

            while True:
                # Read next valid line from reference
                ref_line = None
                while True:
                    line = ref_f.readline()
                    if not line:  # EOF
                        break
                    ref_line_num += 1
                    ref_state = parse_log_line(line)
                    if ref_state:
                        ref_line = line
                        break

                # Read next valid line from test
                test_line = None
                while True:
                    line = test_f.readline()
                    if not line:  # EOF
                        break
                    test_line_num += 1
                    test_state = parse_log_line(line)
                    if test_state:
                        test_line = line
                        break

                # Check if both reached EOF
                if not ref_line and not test_line:
                    return (True, line_num, None, None)

                # Check if one file ended prematurely
                if not ref_line:
                    print(f"ERROR: Reference log ended at line {ref_line_num}, but test log continues")
                    return (False, line_num, None, test_state)

                if not test_line:
                    print(f"ERROR: Test log ended at line {test_line_num}, but reference log continues")
                    return (False, line_num, ref_state, None)

                line_num += 1

                # Compare states
                if ref_state != test_state:
                    return (False, line_num, ref_state, test_state)

    except FileNotFoundError as e:
        print(f"ERROR: File not found: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"ERROR: {e}")
        sys.exit(1)

def print_diff(ref_state: Dict[str, str], test_state: Dict[str, str]):
    """Print differences between two states."""
    print("\nRegister Differences:")
    for key in ref_state:
        if ref_state[key] != test_state[key]:
            print(f"  {key:8s}: Expected {ref_state[key]:>4s}, Got {test_state[key]:>4s}")

def main():
    if len(sys.argv) != 3:
        print("Usage: python3 compare_doctor_logs.py <reference_log> <test_log>")
        sys.exit(1)

    reference_path = sys.argv[1]
    test_path = sys.argv[2]

    print(f"Comparing logs:")
    print(f"  Reference: {reference_path}")
    print(f"  Test:      {test_path}")
    print()

    match, line_num, ref_state, test_state = compare_logs(reference_path, test_path)

    if match:
        print(f"✓ PASS: All {line_num} instructions match!")
        print(f"  The simulator execution matches the reference trace perfectly.")
        return 0
    else:
        print(f"✗ DIVERGENCE at instruction {line_num}")
        print()

        if ref_state and test_state:
            print(f"Expected: {format_state(ref_state)}")
            print(f"Got:      {format_state(test_state)}")
            print_diff(ref_state, test_state)
        elif ref_state:
            print(f"Expected: {format_state(ref_state)}")
            print("Got: <EOF>")
        elif test_state:
            print("Expected: <EOF>")
            print(f"Got:      {format_state(test_state)}")

        print()
        print(f"PC at divergence: {test_state['PC'] if test_state else 'N/A'}")
        print()
        print("Next steps:")
        print("  1. Disassemble instruction at PC using rgbdasm")
        print("  2. Examine VCD trace around this instruction")
        print("  3. Check CPU implementation for this opcode")

        return 1

if __name__ == '__main__':
    sys.exit(main())
