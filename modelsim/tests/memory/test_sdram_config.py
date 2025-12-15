"""
SDRAM Config Register Unit Test

Native Python test class for the SDRAM configuration register.
"""

import sys
import os

# Add parent directories to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from test_framework import IverilogTest


class TestSDRAMConfig(IverilogTest):
    """SDRAM config register unit test using native Python test class."""

    name = "sdram_config"
    category = "memory"
    timeout = 60

    # Source files (relative to project root)
    sources = [
        "Quartus/rtl/sdram/SDRAMConfigRegister.sv",
    ]

    # Testbench (relative to modelsim directory)
    testbench = "sdram_config_tb.sv"

    # Include directories
    includes = [
        "Quartus/rtl",
        "Quartus/rtl/sdram",
    ]

    # Additional flags
    iverilog_flags = ["-g2012", "-Dverilator"]


# Allow running as standalone script
if __name__ == "__main__":
    test = TestSDRAMConfig()
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
