"""
Utility functions for the test framework.
"""

import os
import re
import shutil
from typing import Optional, Tuple


def find_iverilog() -> Optional[str]:
    """Find the iverilog executable."""
    # Check local extraction first
    local_path = "/tmp/iverilog_extract/usr/bin/iverilog"
    if os.path.exists(local_path):
        return local_path

    # Check system PATH
    return shutil.which("iverilog")


def find_vvp() -> Optional[str]:
    """Find the vvp executable."""
    # Check local extraction first
    local_path = "/tmp/iverilog_extract/usr/bin/vvp"
    if os.path.exists(local_path):
        return local_path

    # Check system PATH
    return shutil.which("vvp")


def find_verilator() -> Optional[str]:
    """Find the verilator executable."""
    # Check local extraction first
    local_path = "/tmp/verilator_extract/usr/bin/verilator"
    if os.path.exists(local_path):
        return local_path

    # Check system PATH
    return shutil.which("verilator")


def parse_test_output(output: str) -> Tuple[int, int, int]:
    """
    Parse test output to extract test counts.

    Returns:
        Tuple of (total, passed, failed)
    """
    total = 0
    passed = 0
    failed = 0

    # Try various patterns
    patterns = [
        # "Total Tests: 20\nPassed: 18\nFailed: 2"
        (r'Total\s*Tests?\s*:\s*(\d+)', r'Passed\s*:\s*(\d+)', r'Failed\s*:\s*(\d+)'),
        # "Tests: 20, Pass: 18, Fail: 2"
        (r'Tests?\s*:\s*(\d+)', r'Pass(?:ed)?\s*:\s*(\d+)', r'Fail(?:ed)?\s*:\s*(\d+)'),
        # "run=20 pass=18 fail=2"
        (r'run\s*=\s*(\d+)', r'pass\s*=\s*(\d+)', r'fail\s*=\s*(\d+)'),
    ]

    for total_pat, pass_pat, fail_pat in patterns:
        total_match = re.search(total_pat, output, re.IGNORECASE)
        pass_match = re.search(pass_pat, output, re.IGNORECASE)
        fail_match = re.search(fail_pat, output, re.IGNORECASE)

        if total_match:
            total = int(total_match.group(1))
        if pass_match:
            passed = int(pass_match.group(1))
        if fail_match:
            failed = int(fail_match.group(1))

        if total > 0:
            break

    # If we only found passed/failed, compute total
    if total == 0 and (passed > 0 or failed > 0):
        total = passed + failed

    return total, passed, failed


def check_test_success(output: str, exit_code: int) -> bool:
    """
    Check if a test was successful based on output and exit code.

    Returns:
        True if test passed, False otherwise
    """
    if exit_code != 0:
        return False

    # Check for success indicators
    success_patterns = [
        r'ALL\s*TESTS?\s*PASSED',
        r'SUCCESS',
        r'Pass\s*Rate\s*:\s*100',
        r'Failed\s*:\s*0\b',
        r'✓\s*PASS',              # Unicode pass marker
        r'\bPASS\b\s*$',          # PASS at end of line (final verdict)
    ]

    for pattern in success_patterns:
        if re.search(pattern, output, re.IGNORECASE | re.MULTILINE):
            return True

    # Check for failure indicators
    failure_patterns = [
        r'TESTS?\s*FAILED',
        r'FAILURE',
        r'\bERROR\b(?!\s*:\s*0)',  # ERROR but not "Error: 0" (which means no error)
        r'Failed\s*:\s*[1-9]',
        r'❌\s*FAIL',              # Unicode fail marker
        r'\*\*\*.*FAIL',           # *** FAIL patterns
    ]

    for pattern in failure_patterns:
        if re.search(pattern, output, re.IGNORECASE | re.MULTILINE):
            return False

    # Default to exit code
    return exit_code == 0


def check_skip_conditions(output: str) -> bool:
    """
    Check if test should be skipped based on output.

    Returns:
        True if test should be skipped
    """
    skip_patterns = [
        r'COMPILATION\s*FAILED',
        r'cannot\s*test',
        r'not\s*found',
        r'^\s*SKIP\b',      # SKIP at start of line
        r'\[SKIP\]',        # [SKIP] marker
        r'SKIP\s*:',        # SKIP: prefix
    ]

    for pattern in skip_patterns:
        if re.search(pattern, output, re.IGNORECASE | re.MULTILINE):
            return True

    return False


def get_project_root() -> str:
    """Get the project root directory."""
    # Assuming this file is in modelsim/test_framework/
    current_dir = os.path.dirname(os.path.abspath(__file__))
    modelsim_dir = os.path.dirname(current_dir)
    project_root = os.path.dirname(modelsim_dir)
    return project_root


def get_modelsim_dir() -> str:
    """Get the modelsim directory."""
    current_dir = os.path.dirname(os.path.abspath(__file__))
    return os.path.dirname(current_dir)
