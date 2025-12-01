"""
PIC (8259) Unit Test

Native Python test class for the 8259 Programmable Interrupt Controller.
"""

import sys
import os

# Add parent directories to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from test_framework import IverilogTest


class TestPIC(IverilogTest):
    """8259 PIC unit test using native Python test class."""

    name = "pic"
    category = "peripheral"
    timeout = 60

    # Source files (relative to project root)
    sources = [
        "Quartus/rtl/KF8259/KF8259.sv",
        "Quartus/rtl/KF8259/KF8259_Bus_Control_Logic.sv",
        "Quartus/rtl/KF8259/KF8259_Control_Logic.sv",
        "Quartus/rtl/KF8259/KF8259_Interrupt_Request.sv",
        "Quartus/rtl/KF8259/KF8259_Priority_Resolver.sv",
        "Quartus/rtl/KF8259/KF8259_In_Service.sv",
    ]

    # Testbench (relative to modelsim directory)
    testbench = "pic_tb.sv"

    # Include directories
    includes = [
        "Quartus/rtl",
        "Quartus/rtl/KF8259",
    ]


# Allow running as standalone script
if __name__ == "__main__":
    test = TestPIC()
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
