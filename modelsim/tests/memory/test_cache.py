"""
Cache Unit Test

Native Python test class for the unified cache system.
"""

import sys
import os

# Add parent directories to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from test_framework import IverilogTest


class TestCache(IverilogTest):
    """Cache unit test using native Python test class."""

    name = "cache"
    category = "memory"
    timeout = 120

    # Source files (relative to project root)
    sources = [
        "Quartus/rtl/common/Cache.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/BlockRam.sv",
    ]

    # Testbench (relative to modelsim directory)
    testbench = "cache_tb.sv"

    # Include directories
    includes = [
        "Quartus/rtl",
        "Quartus/rtl/common",
    ]

    # Additional flags
    iverilog_flags = ["-g2012", "-Dverilator"]


# Allow running as standalone script
if __name__ == "__main__":
    test = TestCache()
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
