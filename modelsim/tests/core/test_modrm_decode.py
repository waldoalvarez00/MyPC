"""
ModRMDecode Unit Test

Native Python test class for x86 ModR/M byte decoding.
"""

import sys
import os

# Add parent directories to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from test_framework import IverilogTest


class TestModRMDecode(IverilogTest):
    """ModRMDecode unit test using native Python test class."""

    name = "modrm_decode"
    category = "core"
    timeout = 60

    # Source files (relative to project root)
    sources = [
        "Quartus/rtl/CPU/ModRMDecode.sv",
    ]

    # Testbench (relative to modelsim directory)
    testbench = "modrm_decode_tb.sv"

    # Include directories
    includes = [
        "Quartus/rtl/CPU",
    ]


# Allow running as standalone script
if __name__ == "__main__":
    test = TestModRMDecode()
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
