"""
SDRAM Controller Unit Test

Native Python test class for the SDRAM controller.
"""

import sys
import os

# Add parent directories to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from test_framework import IverilogTest


class TestSDRAM(IverilogTest):
    """SDRAM controller unit test using native Python test class."""

    name = "sdram"
    category = "memory"
    timeout = 120

    # Source files (relative to project root)
    sources = [
        "Quartus/rtl/sdram/Counter.sv",
        "Quartus/rtl/sdram/SDRAMController.sv",
    ]

    # Testbench (relative to modelsim directory)
    testbench = "sdram_tb.sv"

    # Include directories
    includes = [
        "Quartus/rtl",
        "Quartus/rtl/sdram",
    ]

    # Additional flags
    iverilog_flags = ["-g2012", "-Dverilator"]


# Allow running as standalone script
if __name__ == "__main__":
    test = TestSDRAM()
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
