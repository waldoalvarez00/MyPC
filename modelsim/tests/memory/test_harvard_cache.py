"""
Harvard Cache System Unit Test

Native Python test class for the Harvard architecture cache system.
"""

import sys
import os

# Add parent directories to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from test_framework import IverilogTest


class TestHarvardCache(IverilogTest):
    """Harvard cache system unit test using native Python test class."""

    name = "harvard_cache"
    category = "memory"
    timeout = 120

    # Source files (relative to project root)
    sources = [
        "Quartus/rtl/common/BlockRam.sv",
        "Quartus/rtl/common/DPRam.sv",
        "Quartus/rtl/common/ICache.sv",
        "Quartus/rtl/common/DCache.sv",
        "Quartus/rtl/common/HarvardArbiter.sv",
        "Quartus/rtl/common/HarvardCacheSystem.sv",
    ]

    # Testbench (relative to modelsim directory)
    testbench = "harvard_cache_tb.sv"

    # Include directories
    includes = [
        "Quartus/rtl/common",
        "Quartus/rtl/CPU",
    ]

    # Additional flags - default cache size
    iverilog_flags = ["-g2012", "-DCACHE_LINES=512"]


# Allow running as standalone script
if __name__ == "__main__":
    test = TestHarvardCache()
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
