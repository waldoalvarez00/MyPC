"""
PPI (8255) Unit Test

Native Python test class for the 8255 Programmable Peripheral Interface.
"""

import sys
import os

# Add parent directories to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from test_framework import IverilogTest


class TestPPI(IverilogTest):
    """8255 PPI unit test using native Python test class."""

    name = "ppi"
    category = "peripheral"
    timeout = 60

    # Source files (relative to project root)
    sources = [
        "Quartus/rtl/KF8255/KF8255.sv",
        "Quartus/rtl/KF8255/KF8255_Control_Logic.sv",
        "Quartus/rtl/KF8255/KF8255_Group.sv",
        "Quartus/rtl/KF8255/KF8255_Port.sv",
        "Quartus/rtl/KF8255/KF8255_Port_C.sv",
    ]

    # Testbench (relative to modelsim directory)
    testbench = "ppi_tb.sv"

    # Include directories
    includes = [
        "Quartus/rtl",
        "Quartus/rtl/KF8255",
    ]


# Allow running as standalone script
if __name__ == "__main__":
    test = TestPPI()
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
