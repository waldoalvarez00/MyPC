#!/usr/bin/env python3
"""
Main test runner for MyPC Verilog simulation tests.

Usage:
    python test_runner.py                    # Run all tests
    python test_runner.py --category core    # Run tests in category
    python test_runner.py --test test_alu    # Run specific test
    python test_runner.py --parallel 4       # Run in parallel
    python test_runner.py --list             # List available tests
    python test_runner.py --skip-long        # Skip long-running tests
    python test_runner.py --clean            # Remove test artifacts
"""

import argparse
import glob
import os
import shutil
import sys
import time
import json
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Dict, List, Optional, Tuple
from collections import deque

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from test_framework import TestResult, TestStatus, TestSuite
from test_framework.iverilog_test import IverilogTest
from test_framework.verilator_test import VerilatorTest
from test_framework.python_test import PythonScriptTest
from test_framework.utils import get_modelsim_dir, get_project_root

# Import native test configurations
try:
    from test_configs import TEST_CONFIGS, get_all_tests as get_all_configs
    NATIVE_TESTS_AVAILABLE = True
except ImportError:
    NATIVE_TESTS_AVAILABLE = False

# Estimated test durations (in seconds) based on historical data
# Used for better ETA calculation
TEST_TIME_ESTIMATES = {
    # Fast tests (< 5s)
    'ALU': 1, 'RegisterFile': 1, 'JumpTest': 1, 'modrm_decode': 1,
    'divider': 2, 'arbiter': 1, 'id_arbiter': 1, 'pic': 2, 'ppi': 1,
    'fpu_interface_simple': 1, 'fpu_outer_queue': 1, 'simple_uart': 1,
    'bios_upload_controller': 1, 'bios_upload_integration': 1,
    # New core tests
    'flags': 2, 'immediate_reader': 2, 'ip': 2, 'loop_counter': 2,
    'microcode': 3, 'prefetch': 3, 'segment_register_file': 2, 'temp_reg': 1,
    # Previously untested module tests
    'csipsync': 1, 'segment_override': 1, 'loadstore': 3, 'insndecoder': 1,
    # New peripheral tests
    'fifo': 2, 'kf8253': 5, 'kfps2kb': 3, 'fontcolorlut_unit': 2,
    'msmouse_wrapper': 3, 'speaker_audio_converter': 2,
    'arbiter_tests': 3, 'pipelined_dma_fpu_arbiter': 5,

    # Medium tests (5-30s)
    'cache': 5, 'harvard_cache': 8, 'sdram': 3, 'sdram_config': 3,
    'timer': 15, 'fpu_format_converter': 5, 'format_converter_q262': 3,
    'fpu_interface': 3, 'floppy': 5, 'floppy_dma': 8, 'floppy_sd': 5,
    'floppy_sd_integration': 5, 'dma_arbiter': 3, 'dma_integration': 5,
    'mem_arbiter_extend': 3, 'ps2_keyboard': 5, 'ps2_mouse': 5,
    'ps2_keyboard_protocol': 5, 'ps2_mouse_verilator': 10, 'uart': 5,
    'vgasync_unit': 3, 'floppy_dma_icarus': 8,
    # New FPU tests
    'cordic_correction_integration': 10, 'fstsw_ax': 5, 'fstsw_ax_integration': 8,
    # New cache tests
    'cache_multisize_tests': 15, 'dcache2way_flush': 8, 'dcache2way_simple': 5,
    'dcache_coherency': 10, 'harvard_arbiter': 5, 'harvard_cache_protected': 10,
    'harvard_cache_random': 15, 'harvard_dcache_flush': 8, 'harvard_smc': 10,
    'harvard_smc_mini': 5, 'icache_dcache_coh': 10,
    # Extended PIC tests (kf8259_comprehensive now uses Verilator - fast!)
    'kf8259_all_tests': 10, 'kf8259_comprehensive': 5, 'kf8259_unit_tests': 5,

    # Long tests (30-120s) - will show warning
    'vga': 30, 'vga_modes': 45, 'vga_all_modes': 60, 'vga_mode_switching': 45,
    'vga_complete': 90, 'cga': 30, 'cga_integration': 45, 'vga_unit_tests': 30,
    'vga_framebuffer_integration': 90, 'uart_16750_lite': 30,

    # FPU harness tests (Python scripts)
    'fpu_harness_microseq': 1, 'fpu_harness_microcode': 1,
}

# Tests considered "long" - will show warning and can be skipped
LONG_TESTS = {name for name, duration in TEST_TIME_ESTIMATES.items() if duration >= 30}


def clean_test_artifacts(modelsim_dir: str, verbose: bool = False) -> dict:
    """
    Remove test artifacts from the modelsim directory and related locations.

    Removes:
    - test_results_*/ directories (test logs and JSON results)
    - *.vvp files (Icarus Verilog compiled simulations with extension)
    - *.vcd files (VCD waveform files)
    - *_sim files (compiled simulation binaries)
    - VVP executables without extension (detected by 'bin/vvp' shebang)
    - obj_dir*/ directories (Verilator build directories)
    - __pycache__/ directories (Python bytecode cache)
    - FPU8087 test artifacts (debug_*.txt, tb_* binaries, *.vcd)

    Args:
        modelsim_dir: Path to the modelsim directory
        verbose: Print detailed information about removed files

    Returns:
        Dictionary with counts of removed items by type
    """
    removed = {
        'result_dirs': 0,
        'vvp_files': 0,
        'vcd_files': 0,
        'sim_binaries': 0,
        'obj_dirs': 0,
        'pycache_dirs': 0,
        'fpu_artifacts': 0,
        'total_bytes': 0
    }

    def get_size(path: str) -> int:
        """Get size of file or directory."""
        if os.path.isfile(path):
            return os.path.getsize(path)
        elif os.path.isdir(path):
            total = 0
            for dirpath, dirnames, filenames in os.walk(path):
                for f in filenames:
                    fp = os.path.join(dirpath, f)
                    if os.path.exists(fp):
                        total += os.path.getsize(fp)
            return total
        return 0

    # Remove test_results_* directories
    for item in glob.glob(os.path.join(modelsim_dir, "test_results_*")):
        if os.path.isdir(item):
            size = get_size(item)
            if verbose:
                print(f"  Removing directory: {os.path.basename(item)}")
            shutil.rmtree(item)
            removed['result_dirs'] += 1
            removed['total_bytes'] += size

    # Remove *.vvp files (Icarus Verilog compiled simulations)
    for item in glob.glob(os.path.join(modelsim_dir, "*.vvp")):
        if os.path.isfile(item):
            size = get_size(item)
            if verbose:
                print(f"  Removing file: {os.path.basename(item)}")
            os.remove(item)
            removed['vvp_files'] += 1
            removed['total_bytes'] += size

    # Remove *.vcd files (waveform files)
    for item in glob.glob(os.path.join(modelsim_dir, "*.vcd")):
        if os.path.isfile(item):
            size = get_size(item)
            if verbose:
                print(f"  Removing file: {os.path.basename(item)}")
            os.remove(item)
            removed['vcd_files'] += 1
            removed['total_bytes'] += size

    # Remove *_sim files (compiled simulation binaries without extension)
    # Be careful to only remove files that look like simulation binaries
    for item in glob.glob(os.path.join(modelsim_dir, "*_sim")):
        if os.path.isfile(item) and not item.endswith('.sv') and not item.endswith('.v'):
            # Additional check: should be an executable or at least not a text file
            size = get_size(item)
            if verbose:
                print(f"  Removing file: {os.path.basename(item)}")
            os.remove(item)
            removed['sim_binaries'] += 1
            removed['total_bytes'] += size

    # Remove VVP executables (Icarus Verilog compiled binaries without extension)
    # Detect by content: files starting with "#! /usr/local/bin/vvp" shebang
    # Scan all files without known source extensions
    source_extensions = ('.sv', '.v', '.py', '.sh', '.md', '.txt', '.json', '.yaml', '.yml',
                         '.hex', '.mif', '.bin', '.us', '.tcl', '.do', '.qip', '.qsf', '.sdc')
    for item in os.listdir(modelsim_dir):
        item_path = os.path.join(modelsim_dir, item)
        if os.path.isfile(item_path) and not item.endswith(source_extensions) and not item.startswith('.'):
            try:
                with open(item_path, 'rb') as f:
                    first_bytes = f.read(30)
                    if b'bin/vvp' in first_bytes:
                        size = get_size(item_path)
                        if verbose:
                            print(f"  Removing VVP binary: {item}")
                        os.remove(item_path)
                        removed['sim_binaries'] += 1
                        removed['total_bytes'] += size
            except (IOError, OSError):
                pass  # Skip files we can't read

    # Remove common build artifacts (a.out, test_vectors.*)
    build_artifacts = ["a.out", "test_vectors.txt", "test_vectors.vh"]
    for artifact in build_artifacts:
        item_path = os.path.join(modelsim_dir, artifact)
        if os.path.isfile(item_path):
            size = get_size(item_path)
            if verbose:
                print(f"  Removing build artifact: {artifact}")
            os.remove(item_path)
            removed['sim_binaries'] += 1
            removed['total_bytes'] += size

    # Remove obj_dir* directories (Verilator build directories)
    for item in glob.glob(os.path.join(modelsim_dir, "obj_dir*")):
        if os.path.isdir(item):
            size = get_size(item)
            if verbose:
                print(f"  Removing directory: {os.path.basename(item)}")
            shutil.rmtree(item)
            removed['obj_dirs'] += 1
            removed['total_bytes'] += size

    # Remove __pycache__ directories (Python bytecode cache)
    # Check in modelsim/, modelsim/test_framework/, modelsim/tests/, and FPU8087/
    project_root = os.path.dirname(modelsim_dir)
    pycache_locations = [
        os.path.join(modelsim_dir, "__pycache__"),
        os.path.join(modelsim_dir, "test_framework", "__pycache__"),
        os.path.join(modelsim_dir, "tests", "__pycache__"),
        os.path.join(project_root, "Quartus", "rtl", "FPU8087", "__pycache__"),
    ]
    for pycache_dir in pycache_locations:
        if os.path.isdir(pycache_dir):
            size = get_size(pycache_dir)
            rel_path = os.path.relpath(pycache_dir, project_root)
            if verbose:
                print(f"  Removing directory: {rel_path}")
            shutil.rmtree(pycache_dir)
            removed['pycache_dirs'] += 1
            removed['total_bytes'] += size

    # Remove FPU8087 test artifacts (debug traces, compiled testbenches, vcd files)
    fpu_dir = os.path.join(project_root, "Quartus", "rtl", "FPU8087")
    if os.path.isdir(fpu_dir):
        # debug_*.txt files
        for item in glob.glob(os.path.join(fpu_dir, "debug_*.txt")):
            if os.path.isfile(item):
                size = get_size(item)
                rel_path = os.path.relpath(item, project_root)
                if verbose:
                    print(f"  Removing file: {rel_path}")
                os.remove(item)
                removed['fpu_artifacts'] += 1
                removed['total_bytes'] += size
        # tb_* compiled binaries (vvp scripts without .v extension)
        for item in glob.glob(os.path.join(fpu_dir, "tb_*")):
            if os.path.isfile(item) and not item.endswith('.v') and not item.endswith('.sv'):
                size = get_size(item)
                rel_path = os.path.relpath(item, project_root)
                if verbose:
                    print(f"  Removing file: {rel_path}")
                os.remove(item)
                removed['fpu_artifacts'] += 1
                removed['total_bytes'] += size
        # *.vcd files
        for item in glob.glob(os.path.join(fpu_dir, "*.vcd")):
            if os.path.isfile(item):
                size = get_size(item)
                rel_path = os.path.relpath(item, project_root)
                if verbose:
                    print(f"  Removing file: {rel_path}")
                os.remove(item)
                removed['fpu_artifacts'] += 1
                removed['total_bytes'] += size

    return removed


def format_bytes(size: int) -> str:
    """Format byte count as human-readable string."""
    for unit in ['B', 'KB', 'MB', 'GB']:
        if size < 1024:
            return f"{size:.1f} {unit}"
        size /= 1024
    return f"{size:.1f} TB"


class ETACalculator:
    """Improved ETA calculator using weighted moving average."""

    def __init__(self, total_tests: int, time_estimates: Dict[str, float]):
        self.total_tests = total_tests
        self.time_estimates = time_estimates
        self.completed = 0
        self.actual_times: List[float] = []
        self.start_time = datetime.now()
        self.remaining_estimates: List[float] = []

    def set_test_order(self, tests: List):
        """Set the order of tests to estimate remaining time."""
        self.remaining_estimates = []
        for test in tests:
            estimate = self.time_estimates.get(test.name, 10)  # Default 10s
            self.remaining_estimates.append(estimate)

    def record_completion(self, test_name: str, actual_duration: float):
        """Record a completed test and update estimates."""
        self.completed += 1
        self.actual_times.append(actual_duration)

        # Update estimate for this test type if we have actual data
        estimated = self.time_estimates.get(test_name, 10)
        if estimated > 0:
            # Blend actual with estimate
            self.time_estimates[test_name] = 0.7 * actual_duration + 0.3 * estimated

        # Remove from remaining
        if self.remaining_estimates:
            self.remaining_estimates.pop(0)

    def get_eta(self) -> Tuple[float, str]:
        """Get estimated time remaining."""
        if self.completed == 0:
            # Use sum of estimates for remaining tests
            eta_seconds = sum(self.remaining_estimates)
        else:
            # Use weighted average of actual times and remaining estimates
            avg_actual = sum(self.actual_times) / len(self.actual_times)

            # Adjust remaining estimates based on actual performance
            if self.actual_times:
                first_n = min(5, len(self.actual_times))
                first_n_sum = sum(self.actual_times[:first_n])
                if first_n_sum > 0:
                    adjustment = avg_actual / (first_n_sum / first_n)
                else:
                    adjustment = 1.0
            else:
                adjustment = 1.0

            eta_seconds = sum(self.remaining_estimates) * min(adjustment, 2.0)

        # Format as MM:SS or HH:MM:SS
        if eta_seconds >= 3600:
            hours = int(eta_seconds // 3600)
            minutes = int((eta_seconds % 3600) // 60)
            seconds = int(eta_seconds % 60)
            eta_str = f"{hours:02d}:{minutes:02d}:{seconds:02d}"
        else:
            minutes = int(eta_seconds // 60)
            seconds = int(eta_seconds % 60)
            eta_str = f"{minutes:02d}:{seconds:02d}"

        return eta_seconds, eta_str

    def get_total_estimate(self) -> str:
        """Get total estimated time for all tests."""
        total = sum(self.remaining_estimates)
        if total >= 3600:
            return f"{total/3600:.1f} hours"
        elif total >= 60:
            return f"{total/60:.1f} minutes"
        else:
            return f"{total:.0f} seconds"


class TestRunner:
    """Main test runner that discovers and executes tests."""

    def __init__(self, enable_coverage: bool = False):
        self.tests: Dict[str, List] = {}  # category -> list of tests
        self.suite = TestSuite(name="MyPC2 Test Suite")
        self.modelsim_dir = get_modelsim_dir()
        self.project_root = get_project_root()
        self.results_dir = ""
        self.eta_calculator = None
        self.skip_long = False
        self.enable_coverage = enable_coverage  # Enable Verilator code coverage

    def discover_native_tests(self):
        """Discover tests using native Python configurations (no shell scripts)."""
        if not NATIVE_TESTS_AVAILABLE:
            print("Warning: Native test configurations not available")
            return

        for name, config in TEST_CONFIGS.items():
            category = config.category
            if category not in self.tests:
                self.tests[category] = []

            # Check simulator type and create appropriate test
            simulator = getattr(config, 'simulator', 'iverilog')

            if simulator == 'verilator':
                # Create VerilatorTest from TestConfig
                # Enable coverage if runner has coverage enabled or config specifies it
                coverage = self.enable_coverage or getattr(config, 'enable_coverage', False)
                test = VerilatorTest(
                    name=config.name,
                    sources=config.sources,
                    includes=config.includes,
                    top_module=config.top_module,
                    cpp_testbench=getattr(config, 'cpp_testbench', ''),
                    category=config.category,
                    timeout=config.timeout,
                    enable_coverage=coverage
                )
            elif simulator == 'python':
                # Create PythonScriptTest from TestConfig
                test = PythonScriptTest(
                    name=config.name,
                    script=getattr(config, 'script', ''),
                    work_dir=getattr(config, 'work_dir', ''),
                    script_args=getattr(config, 'script_args', []),
                    category=config.category,
                    timeout=config.timeout
                )
            else:
                # Create IverilogTest from TestConfig
                test = IverilogTest(
                    name=config.name,
                    testbench=config.testbench,
                    sources=config.sources,
                    includes=config.includes,
                    defines=config.defines,
                    top_module=config.top_module,
                    category=config.category,
                    timeout=config.timeout
                )
            self.tests[category].append(test)

    def get_all_tests(self, skip_long: bool = False) -> List:
        """Get flat list of all tests."""
        all_tests = []
        for tests in self.tests.values():
            for test in tests:
                if skip_long and test.name in LONG_TESTS:
                    continue
                all_tests.append(test)
        return all_tests

    def get_tests_by_category(self, category: str) -> List:
        """Get tests in a specific category."""
        return self.tests.get(category, [])

    def get_test_by_name(self, name: str) -> Optional[object]:
        """Find a test by name."""
        # First pass: exact match
        for tests in self.tests.values():
            for test in tests:
                if test.name == name:
                    return test
        # Second pass: partial match (search term in test name)
        for tests in self.tests.values():
            for test in tests:
                if name in test.name:
                    return test
        return None

    def create_results_directory(self):
        """Create directory for test results."""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.results_dir = os.path.join(
            self.modelsim_dir, f"test_results_{timestamp}"
        )
        os.makedirs(self.results_dir, exist_ok=True)

    def run_single_test(self, test, verbose=False) -> TestResult:
        """Run a single test and return result."""
        if verbose:
            print(f"Running: {test.name}...")

        # Check if test should be skipped
        if test.category == "skip":
            result = TestResult(
                name=test.name,
                status=TestStatus.SKIP,
                output=f"Test skipped (category='skip')",
                duration=0.0
            )
            result.category = test.category

            # Save log file
            if self.results_dir:
                log_file = os.path.join(self.results_dir, f"{test.name}.log")
                with open(log_file, 'w') as f:
                    f.write(f"Test: {test.name}\n")
                    f.write(f"Category: {test.category}\n")
                    f.write(f"Status: {result.status.value}\n")
                    f.write(f"Duration: {result.duration:.2f}s\n")
                    f.write("\n--- Output ---\n")
                    f.write(result.output)
                result.log_file = log_file

            return result

        result = test.execute()
        result.category = test.category

        # Save log file
        if self.results_dir:
            log_file = os.path.join(self.results_dir, f"{test.name}.log")
            with open(log_file, 'w') as f:
                f.write(f"Test: {test.name}\n")
                f.write(f"Category: {test.category}\n")
                f.write(f"Status: {result.status.value}\n")
                f.write(f"Duration: {result.duration:.2f}s\n")
                f.write("\n--- Output ---\n")
                f.write(result.output)
                if result.error:
                    f.write("\n--- Errors ---\n")
                    f.write(result.error)
            result.log_file = log_file

        return result

    def run_tests(self, tests: List, parallel: int = 1, verbose: bool = False):
        """
        Run a list of tests.

        Args:
            tests: List of test objects to run
            parallel: Number of parallel workers (1 = sequential)
            verbose: Print verbose output
        """
        self.suite.start_time = datetime.now()
        total = len(tests)
        completed = 0

        # Initialize ETA calculator
        self.eta_calculator = ETACalculator(total, TEST_TIME_ESTIMATES.copy())
        self.eta_calculator.set_test_order(tests)

        if parallel > 1:
            # Parallel execution
            with ThreadPoolExecutor(max_workers=parallel) as executor:
                futures = {
                    executor.submit(self.run_single_test, test, verbose): test
                    for test in tests
                }

                for future in as_completed(futures):
                    test = futures[future]
                    try:
                        result = future.result()
                        self.suite.add_result(result)
                        completed += 1
                        self.eta_calculator.record_completion(test.name, result.duration)
                        self._print_progress(result, completed, total)
                    except Exception as e:
                        error_result = TestResult(
                            name=test.name,
                            status=TestStatus.ERROR,
                            error=str(e),
                            category=test.category
                        )
                        self.suite.add_result(error_result)
                        completed += 1
                        self.eta_calculator.record_completion(test.name, 0)
                        self._print_progress(error_result, completed, total)
        else:
            # Sequential execution
            for test in tests:
                # Show warning for long tests
                if test.name in LONG_TESTS:
                    estimate = TEST_TIME_ESTIMATES.get(test.name, 30)
                    print(f"  [!] Long test: {test.name} (~{estimate}s)")

                result = self.run_single_test(test, verbose)
                self.suite.add_result(result)
                completed += 1
                self.eta_calculator.record_completion(test.name, result.duration)
                self._print_progress(result, completed, total)

        self.suite.end_time = datetime.now()

    def _print_progress(self, result: TestResult, completed: int, total: int):
        """Print progress line for a test result."""
        status_labels = {
            TestStatus.PASS: "PASS",
            TestStatus.FAIL: "FAIL",
            TestStatus.SKIP: "SKIP",
            TestStatus.ERROR: "ERR ",
            TestStatus.TIMEOUT: "TIME",
        }
        status = status_labels.get(result.status, "????")

        # Get ETA from calculator
        _, eta_str = self.eta_calculator.get_eta()

        print(f"{status} {result.name:<40} | "
              f"{completed}/{total} | "
              f"{result.duration:.1f}s | "
              f"ETA: {eta_str}")

        # Show failure details
        if result.status in (TestStatus.FAIL, TestStatus.ERROR):
            if result.error:
                # Show last few lines of error
                lines = result.error.strip().split('\n')[-5:]
                for line in lines:
                    print(f"    {line}")

    def print_summary(self):
        """Print test suite summary."""
        self.suite.print_summary()

    def save_results(self, output_file: Optional[str] = None):
        """Save results to JSON file."""
        if output_file:
            filepath = output_file
        elif self.results_dir:
            filepath = os.path.join(self.results_dir, "results.json")
        else:
            return

        with open(filepath, 'w') as f:
            f.write(self.suite.to_json())
        print(f"Results saved to: {filepath}")

    def list_tests(self, show_times: bool = True):
        """Print list of available tests."""
        print("\nAvailable Tests:")
        print("=" * 70)

        total_time = 0
        for category, tests in sorted(self.tests.items()):
            cat_time = sum(TEST_TIME_ESTIMATES.get(t.name, 10) for t in tests)
            total_time += cat_time
            print(f"\n{category.upper()} ({len(tests)} tests, ~{cat_time}s):")
            for test in tests:
                est = TEST_TIME_ESTIMATES.get(test.name, 10)
                long_marker = " [LONG]" if test.name in LONG_TESTS else ""
                if show_times:
                    print(f"  - {test.name:<35} (~{est}s){long_marker}")
                else:
                    print(f"  - {test.name}{long_marker}")

        print(f"\nTotal: {len(self.get_all_tests())} tests")
        if total_time >= 3600:
            print(f"Estimated total time: {total_time/3600:.1f} hours")
        else:
            print(f"Estimated total time: {total_time/60:.1f} minutes")

        long_count = sum(1 for t in self.get_all_tests() if t.name in LONG_TESTS)
        if long_count > 0:
            print(f"\nNote: {long_count} long-running tests can be skipped with --skip-long")


def main():
    parser = argparse.ArgumentParser(
        description="MyPC2 Verilog Test Runner",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python test_runner.py                    # Run all tests
  python test_runner.py --skip-long        # Skip tests > 30s
  python test_runner.py -c core -p 4       # Run core tests in parallel
  python test_runner.py --clean            # Remove test artifacts
  python test_runner.py --clean --dry-run  # Preview what would be cleaned
  python test_runner.py --clean -v         # Clean with verbose output
        """
    )

    parser.add_argument(
        '--category', '-c',
        help="Run tests in specific category"
    )
    parser.add_argument(
        '--test', '-t',
        help="Run specific test by name"
    )
    parser.add_argument(
        '--parallel', '-p',
        type=int, default=1,
        help="Number of parallel test workers"
    )
    parser.add_argument(
        '--output', '-o',
        help="Output file for JSON results"
    )
    parser.add_argument(
        '--list', '-l',
        action='store_true',
        help="List available tests"
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help="Verbose output"
    )
    parser.add_argument(
        '--skip-long',
        action='store_true',
        help="Skip long-running tests (> 30s estimated)"
    )
    parser.add_argument(
        '--coverage',
        action='store_true',
        help="Enable Verilator code coverage (line + toggle)"
    )
    parser.add_argument(
        '--clean',
        action='store_true',
        help="Remove test artifacts (results, .vvp, .vcd, obj_dir, etc.)"
    )
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help="Show what would be cleaned without removing (use with --clean)"
    )

    args = parser.parse_args()

    # Handle clean command
    if args.clean:
        modelsim_dir = get_modelsim_dir()
        print("=" * 70)
        print("CLEANING TEST ARTIFACTS")
        print("=" * 70)
        print(f"Directory: {modelsim_dir}")
        print()

        if args.dry_run:
            # Show what would be cleaned without removing
            print("DRY RUN - showing what would be removed:")
            print()

            # Count artifacts
            result_dirs = glob.glob(os.path.join(modelsim_dir, "test_results_*"))
            vvp_files = glob.glob(os.path.join(modelsim_dir, "*.vvp"))
            vcd_files = glob.glob(os.path.join(modelsim_dir, "*.vcd"))
            sim_files = [f for f in glob.glob(os.path.join(modelsim_dir, "*_sim"))
                        if os.path.isfile(f) and not f.endswith('.sv') and not f.endswith('.v')]
            # Also find VVP executables by content (shebang detection)
            source_extensions = ('.sv', '.v', '.py', '.sh', '.md', '.txt', '.json', '.yaml', '.yml',
                                 '.hex', '.mif', '.bin', '.us', '.tcl', '.do', '.qip', '.qsf', '.sdc')
            for item in os.listdir(modelsim_dir):
                item_path = os.path.join(modelsim_dir, item)
                if os.path.isfile(item_path) and not item.endswith(source_extensions) and not item.startswith('.'):
                    try:
                        with open(item_path, 'rb') as f:
                            first_bytes = f.read(30)
                            if b'bin/vvp' in first_bytes:
                                sim_files.append(item_path)
                    except (IOError, OSError):
                        pass
            obj_dirs = glob.glob(os.path.join(modelsim_dir, "obj_dir*"))
            # Check __pycache__ directories
            project_root = os.path.dirname(modelsim_dir)
            pycache_dirs = [p for p in [
                os.path.join(modelsim_dir, "__pycache__"),
                os.path.join(modelsim_dir, "test_framework", "__pycache__"),
                os.path.join(modelsim_dir, "tests", "__pycache__"),
                os.path.join(project_root, "Quartus", "rtl", "FPU8087", "__pycache__"),
            ] if os.path.isdir(p)]

            if result_dirs:
                print(f"Result directories ({len(result_dirs)}):")
                for d in result_dirs[:5]:
                    print(f"  {os.path.basename(d)}/")
                if len(result_dirs) > 5:
                    print(f"  ... and {len(result_dirs) - 5} more")

            if vvp_files:
                print(f"\n.vvp files ({len(vvp_files)}):")
                for f in vvp_files[:5]:
                    print(f"  {os.path.basename(f)}")
                if len(vvp_files) > 5:
                    print(f"  ... and {len(vvp_files) - 5} more")

            if vcd_files:
                print(f"\n.vcd files ({len(vcd_files)}):")
                for f in vcd_files[:5]:
                    print(f"  {os.path.basename(f)}")
                if len(vcd_files) > 5:
                    print(f"  ... and {len(vcd_files) - 5} more")

            if sim_files:
                print(f"\nSimulation binaries ({len(sim_files)}):")
                for f in sim_files[:5]:
                    print(f"  {os.path.basename(f)}")
                if len(sim_files) > 5:
                    print(f"  ... and {len(sim_files) - 5} more")

            if obj_dirs:
                print(f"\nVerilator obj_dir directories ({len(obj_dirs)}):")
                for d in obj_dirs[:5]:
                    print(f"  {os.path.basename(d)}/")
                if len(obj_dirs) > 5:
                    print(f"  ... and {len(obj_dirs) - 5} more")

            if pycache_dirs:
                print(f"\n__pycache__ directories ({len(pycache_dirs)}):")
                for d in pycache_dirs:
                    rel_path = os.path.relpath(d, project_root)
                    print(f"  {rel_path}/")

            # Check FPU8087 artifacts
            fpu_dir = os.path.join(project_root, "Quartus", "rtl", "FPU8087")
            fpu_artifacts = []
            if os.path.isdir(fpu_dir):
                fpu_artifacts.extend(glob.glob(os.path.join(fpu_dir, "debug_*.txt")))
                fpu_artifacts.extend([f for f in glob.glob(os.path.join(fpu_dir, "tb_*"))
                                     if os.path.isfile(f) and not f.endswith('.v') and not f.endswith('.sv')])
                fpu_artifacts.extend(glob.glob(os.path.join(fpu_dir, "*.vcd")))

            if fpu_artifacts:
                print(f"\nFPU8087 artifacts ({len(fpu_artifacts)}):")
                for f in fpu_artifacts:
                    rel_path = os.path.relpath(f, project_root)
                    print(f"  {rel_path}")

            total = len(result_dirs) + len(vvp_files) + len(vcd_files) + len(sim_files) + len(obj_dirs) + len(pycache_dirs) + len(fpu_artifacts)
            if total == 0:
                print("No artifacts found to clean.")
            else:
                print(f"\nTotal items that would be removed: {total}")
                print("\nRun without --dry-run to actually remove these files.")
            return 0
        else:
            # Actually clean
            print("Removing artifacts...")
            removed = clean_test_artifacts(modelsim_dir, verbose=args.verbose)

            print()
            print("=" * 70)
            print("CLEANUP SUMMARY")
            print("=" * 70)
            print(f"Result directories removed: {removed['result_dirs']}")
            print(f".vvp files removed:         {removed['vvp_files']}")
            print(f".vcd files removed:         {removed['vcd_files']}")
            print(f"Simulation binaries:        {removed['sim_binaries']}")
            print(f"Verilator obj_dir removed:  {removed['obj_dirs']}")
            print(f"__pycache__ dirs removed:   {removed['pycache_dirs']}")
            print(f"FPU8087 artifacts removed:  {removed['fpu_artifacts']}")
            print(f"Total space freed:          {format_bytes(removed['total_bytes'])}")
            print("=" * 70)
            return 0

    # Create runner and discover tests
    runner = TestRunner(enable_coverage=args.coverage)

    if not NATIVE_TESTS_AVAILABLE:
        print("Error: Test configurations not available (test_configs.py not found)")
        return 1
    runner.discover_native_tests()

    # List tests if requested
    if args.list:
        runner.list_tests()
        return 0

    # Create results directory
    runner.create_results_directory()

    # Determine which tests to run
    if args.test:
        test = runner.get_test_by_name(args.test)
        if not test:
            print(f"Test not found: {args.test}")
            return 1
        tests = [test]
    elif args.category:
        tests = runner.get_tests_by_category(args.category)
        if not tests:
            print(f"No tests found in category: {args.category}")
            return 1
        # Filter long tests if requested
        if args.skip_long:
            tests = [t for t in tests if t.name not in LONG_TESTS]
    else:
        tests = runner.get_all_tests(skip_long=args.skip_long)

    if not tests:
        print("No tests to run")
        return 1

    # Calculate estimated time
    eta_calc = ETACalculator(len(tests), TEST_TIME_ESTIMATES.copy())
    eta_calc.set_test_order(tests)
    total_estimate = eta_calc.get_total_estimate()

    # Count long tests
    long_tests = [t for t in tests if t.name in LONG_TESTS]

    # Print header
    print("=" * 70)
    print("MYPC2 TEST RUNNER")
    print("=" * 70)
    print(f"Tests to run: {len(tests)}")
    print(f"Estimated time: {total_estimate}")
    if long_tests:
        print(f"Long tests included: {len(long_tests)}")
        if not args.skip_long:
            print("  (use --skip-long to skip these)")
    print(f"Parallel workers: {args.parallel}")
    if args.coverage:
        print(f"Coverage: ENABLED (Verilator tests only)")
    print(f"Results directory: {runner.results_dir}")
    print("=" * 70)
    print()

    # Run tests
    runner.run_tests(tests, parallel=args.parallel, verbose=args.verbose)

    # Print summary
    runner.print_summary()

    # Save results
    runner.save_results(args.output)

    # Return appropriate exit code
    return 0 if runner.suite.failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
