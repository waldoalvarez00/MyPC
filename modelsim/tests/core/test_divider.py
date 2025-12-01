"""
Divider Unit Test

Native Python test class for DIV/IDIV instruction implementation.

NOTE: This test is currently skipped because Icarus Verilog doesn't support
all SystemVerilog constructs used in Divider.sv (enum type assignments in
always_comb, constant selects in always_* processes).
"""

import sys
import os

# Add parent directories to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from test_framework import IverilogTest


class TestDivider(IverilogTest):
    """Divider unit test using native Python test class."""

    name = "divider"
    category = "core"
    timeout = 60

    # Source files (relative to project root)
    sources = [
        "Quartus/rtl/CPU/RegisterEnum.sv",
        "Quartus/rtl/CPU/FlagsEnum.sv",
        "Quartus/rtl/CPU/MicrocodeTypes.sv",
        "Quartus/rtl/CPU/Divider.sv",
    ]

    # Testbench (relative to modelsim directory)
    testbench = "divider_tb.sv"

    # Include directories
    includes = [
        "Quartus/rtl/CPU",
    ]

    def compile(self) -> bool:
        """
        Override compile to skip - Icarus Verilog doesn't support
        all SystemVerilog constructs used in Divider.sv.
        """
        print("NOTE: Divider test requires Verilator (iverilog incompatible)")
        print("Skipping compilation...")
        return True

    def run_simulation(self) -> tuple:
        """Skip simulation with informative message."""
        return (0, "SKIPPED: Divider test requires Verilator\n"
                   "Icarus Verilog doesn't support all SystemVerilog constructs "
                   "used in Divider.sv\n"
                   "Total: 0, Pass: 0, Fail: 0, Skip: 1", "")


# Allow running as standalone script
if __name__ == "__main__":
    test = TestDivider()
    result = test.execute()

    print(f"\nTest: {result.name}")
    print(f"Status: {result.status.value}")
    print(f"Duration: {result.duration:.2f}s")
    print(f"Tests Run: {result.tests_run}")
    print(f"Tests Passed: {result.tests_passed}")
    print(f"Tests Failed: {result.tests_failed}")

    if result.error:
        print(f"\nErrors:\n{result.error}")

    sys.exit(0 if result.status.value == "pass" else 1)
