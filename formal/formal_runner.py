#!/usr/bin/env python3
"""
Formal verification test runner for MyPC2.

Usage:
    python formal_runner.py                    # Run all formal tests
    python formal_runner.py --category arbiter # Run tests in category
    python formal_runner.py --test ICache2Way  # Run specific test
    python formal_runner.py --parallel 4       # Run in parallel
    python formal_runner.py --list             # List available tests
    python formal_runner.py --skip-long        # Skip long-running tests
"""

import argparse
import os
import sys
import subprocess
import time
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Dict, List, Optional, Tuple
from enum import Enum


class TestStatus(Enum):
    PASS = "pass"
    FAIL = "fail"
    ERROR = "error"
    TIMEOUT = "timeout"
    SKIP = "skip"


# Estimated test durations (in seconds) based on typical formal verification times
# These are rough estimates - formal verification times can vary significantly
TEST_TIME_ESTIMATES = {
    # Fast tests (< 30s)
    'DMAArbiter': 10,
    'IDArbiter': 10,
    'MemArbiter': 15,
    'MemArbiterExtend': 15,
    'PipelinedDMAArbiter': 20,
    'PipelinedDMAFPUArbiter': 25,
    'PipelinedMemArbiterExtend': 20,
    'CacheArbiter': 20,
    'DCacheFrontendArbiter': 20,
    'Flags': 15,
    'RegisterFile': 10,

    # Medium tests (30-120s)
    'ICache2Way': 45,
    'ICache2Way_inval': 60,
    'DCache2Way': 60,
    'DCache2Way_MemArbiter': 90,
    'DCache2Way_loose': 60,
    'DCache2Way_tight': 120,
    'Microcode': 45,
    'LoadStore': 60,
    'Prefetch': 45,

    # FPU tests
    'FPU_Instruction_Queue': 20,
    'FPU_RegisterStack': 25,
    'FPU_Exception_Handler': 20,
    'FPU_CPU_Interface': 45,
    'FPU_IEEE754_AddSub': 60,
    'FPU_IEEE754_MulDiv_Unified': 90,
    'FPU_SQRT_Newton': 120,
    'FPU_Format_Converter_Unified': 30,
    'FPU_Range_Reduction': 60,
    'FPU_Polynomial_Evaluator': 45,
}

# Tests considered "long" - will show warning and can be skipped
LONG_TESTS = {name for name, duration in TEST_TIME_ESTIMATES.items() if duration >= 60}

# Test categories for organization
TEST_CATEGORIES = {
    'arbiter': [
        'DMAArbiter',
        'IDArbiter',
        'MemArbiter',
        'MemArbiterExtend',
        'PipelinedDMAArbiter',
        'PipelinedDMAFPUArbiter',
        'PipelinedMemArbiterExtend',
        'CacheArbiter',
        'DCacheFrontendArbiter',
    ],
    'cache': [
        'ICache2Way',
        'ICache2Way_inval',
        'DCache2Way',
        'DCache2Way_MemArbiter',
        'DCache2Way_loose',
        'DCache2Way_tight',
    ],
    'cpu': [
        'Microcode',
        'LoadStore',
        'Prefetch',
        'Flags',
        'RegisterFile',
    ],
    'fpu': [
        'FPU_Instruction_Queue',
        'FPU_RegisterStack',
        'FPU_Exception_Handler',
        'FPU_CPU_Interface',
        'FPU_IEEE754_AddSub',
        'FPU_IEEE754_MulDiv_Unified',
        'FPU_SQRT_Newton',
        'FPU_Format_Converter_Unified',
        'FPU_Range_Reduction',
        'FPU_Polynomial_Evaluator',
    ],
}


class FormalTestResult:
    """Result of a formal verification test."""

    def __init__(self, name: str, status: TestStatus, duration: float = 0,
                 output: str = "", error: str = "", category: str = ""):
        self.name = name
        self.status = status
        self.duration = duration
        self.output = output
        self.error = error
        self.category = category
        self.log_file = ""


class ETACalculator:
    """ETA calculator using weighted moving average."""

    def __init__(self, total_tests: int, time_estimates: Dict[str, float]):
        self.total_tests = total_tests
        self.time_estimates = time_estimates
        self.completed = 0
        self.actual_times: List[float] = []
        self.start_time = datetime.now()
        self.remaining_estimates: List[float] = []

    def set_test_order(self, tests: List[str]):
        """Set the order of tests to estimate remaining time."""
        self.remaining_estimates = []
        for test in tests:
            estimate = self.time_estimates.get(test, 30)  # Default 30s
            self.remaining_estimates.append(estimate)

    def record_completion(self, test_name: str, actual_duration: float):
        """Record a completed test and update estimates."""
        self.completed += 1
        self.actual_times.append(actual_duration)

        # Update estimate for this test type if we have actual data
        estimated = self.time_estimates.get(test_name, 30)
        if estimated > 0:
            # Blend actual with estimate
            self.time_estimates[test_name] = 0.7 * actual_duration + 0.3 * estimated

        # Remove from remaining
        if self.remaining_estimates:
            self.remaining_estimates.pop(0)

    def get_eta(self) -> Tuple[float, str]:
        """Get estimated time remaining."""
        if self.completed == 0:
            eta_seconds = sum(self.remaining_estimates)
        else:
            avg_actual = sum(self.actual_times) / len(self.actual_times)
            if self.actual_times:
                adjustment = avg_actual / (sum(self.actual_times[:min(5, len(self.actual_times))]) / min(5, len(self.actual_times)))
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


class FormalTestRunner:
    """Main formal verification test runner."""

    def __init__(self):
        self.formal_dir = os.path.dirname(os.path.abspath(__file__))
        self.project_root = os.path.dirname(self.formal_dir)
        self.tests: Dict[str, List[str]] = {}  # category -> list of test names
        self.results: List[FormalTestResult] = []
        self.results_dir = ""
        self.eta_calculator = None

    def discover_tests(self):
        """Discover all .sby files in the formal directory."""
        # First, organize by category
        for category, tests in TEST_CATEGORIES.items():
            self.tests[category] = []
            for test in tests:
                sby_file = os.path.join(self.formal_dir, f"{test}.sby")
                if os.path.exists(sby_file):
                    self.tests[category].append(test)

        # Find any uncategorized tests
        all_categorized = set()
        for tests in TEST_CATEGORIES.values():
            all_categorized.update(tests)

        uncategorized = []
        for filename in os.listdir(self.formal_dir):
            if filename.endswith('.sby'):
                test_name = filename[:-4]  # Remove .sby
                if test_name not in all_categorized:
                    uncategorized.append(test_name)

        if uncategorized:
            self.tests['other'] = sorted(uncategorized)

    def get_all_tests(self, skip_long: bool = False) -> List[str]:
        """Get flat list of all test names."""
        all_tests = []
        for tests in self.tests.values():
            for test in tests:
                if skip_long and test in LONG_TESTS:
                    continue
                all_tests.append(test)
        return all_tests

    def get_tests_by_category(self, category: str) -> List[str]:
        """Get tests in a specific category."""
        return self.tests.get(category, [])

    def get_test_category(self, test_name: str) -> str:
        """Get the category for a test."""
        for category, tests in self.tests.items():
            if test_name in tests:
                return category
        return "other"

    def create_results_directory(self):
        """Create directory for test results."""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.results_dir = os.path.join(
            self.formal_dir, f"formal_results_{timestamp}"
        )
        os.makedirs(self.results_dir, exist_ok=True)

    def run_single_test(self, test_name: str, verbose: bool = False) -> FormalTestResult:
        """Run a single formal verification test."""
        sby_file = os.path.join(self.formal_dir, f"{test_name}.sby")

        if not os.path.exists(sby_file):
            return FormalTestResult(
                name=test_name,
                status=TestStatus.ERROR,
                error=f"SBY file not found: {sby_file}",
                category=self.get_test_category(test_name)
            )

        start_time = time.time()

        try:
            # Run SymbiYosys with temporary workdir (-t) and force overwrite (-f)
            cmd = ["sby", "-t", "-f", f"formal/{test_name}.sby"]

            if verbose:
                print(f"Running: {' '.join(cmd)}")

            result = subprocess.run(
                cmd,
                cwd=self.project_root,
                capture_output=True,
                text=True,
                timeout=600  # 10 minute timeout
            )

            duration = time.time() - start_time

            # Determine status from return code and output
            if result.returncode == 0:
                status = TestStatus.PASS
            else:
                # Check for specific failure patterns
                if "FAIL" in result.stdout or "FAIL" in result.stderr:
                    status = TestStatus.FAIL
                else:
                    status = TestStatus.ERROR

            test_result = FormalTestResult(
                name=test_name,
                status=status,
                duration=duration,
                output=result.stdout,
                error=result.stderr,
                category=self.get_test_category(test_name)
            )

        except subprocess.TimeoutExpired:
            duration = time.time() - start_time
            test_result = FormalTestResult(
                name=test_name,
                status=TestStatus.TIMEOUT,
                duration=duration,
                error="Test timed out after 600 seconds",
                category=self.get_test_category(test_name)
            )
        except Exception as e:
            duration = time.time() - start_time
            test_result = FormalTestResult(
                name=test_name,
                status=TestStatus.ERROR,
                duration=duration,
                error=str(e),
                category=self.get_test_category(test_name)
            )

        # Save log file
        if self.results_dir:
            log_file = os.path.join(self.results_dir, f"{test_name}.log")
            with open(log_file, 'w') as f:
                f.write(f"Test: {test_name}\n")
                f.write(f"Category: {test_result.category}\n")
                f.write(f"Status: {test_result.status.value}\n")
                f.write(f"Duration: {test_result.duration:.2f}s\n")
                f.write("\n--- Output ---\n")
                f.write(test_result.output)
                if test_result.error:
                    f.write("\n--- Errors ---\n")
                    f.write(test_result.error)
            test_result.log_file = log_file

        return test_result

    def run_tests(self, tests: List[str], parallel: int = 1, verbose: bool = False):
        """Run a list of formal verification tests."""
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
                        self.results.append(result)
                        completed += 1
                        self.eta_calculator.record_completion(test, result.duration)
                        self._print_progress(result, completed, total)
                    except Exception as e:
                        error_result = FormalTestResult(
                            name=test,
                            status=TestStatus.ERROR,
                            error=str(e),
                            category=self.get_test_category(test)
                        )
                        self.results.append(error_result)
                        completed += 1
                        self.eta_calculator.record_completion(test, 0)
                        self._print_progress(error_result, completed, total)
        else:
            # Sequential execution
            for test in tests:
                # Show warning for long tests
                if test in LONG_TESTS:
                    estimate = TEST_TIME_ESTIMATES.get(test, 60)
                    print(f"  [!] Long test: {test} (~{estimate}s)")

                result = self.run_single_test(test, verbose)
                self.results.append(result)
                completed += 1
                self.eta_calculator.record_completion(test, result.duration)
                self._print_progress(result, completed, total)

    def _print_progress(self, result: FormalTestResult, completed: int, total: int):
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

        print(f"{status} {result.name:<30} | "
              f"{completed}/{total} | "
              f"{result.duration:.1f}s | "
              f"ETA: {eta_str}")

        # Show failure details
        if result.status in (TestStatus.FAIL, TestStatus.ERROR):
            if result.error:
                lines = result.error.strip().split('\n')[-5:]
                for line in lines:
                    print(f"    {line}")

    def print_summary(self):
        """Print test suite summary."""
        passed = sum(1 for r in self.results if r.status == TestStatus.PASS)
        failed = sum(1 for r in self.results if r.status == TestStatus.FAIL)
        errors = sum(1 for r in self.results if r.status == TestStatus.ERROR)
        timeouts = sum(1 for r in self.results if r.status == TestStatus.TIMEOUT)
        total = len(self.results)

        total_duration = sum(r.duration for r in self.results)

        print("\n" + "=" * 70)
        print("FORMAL VERIFICATION SUMMARY")
        print("=" * 70)
        print(f"Total:    {total}")
        print(f"Passed:   {passed}")
        print(f"Failed:   {failed}")
        print(f"Errors:   {errors}")
        print(f"Timeouts: {timeouts}")
        print(f"Duration: {total_duration:.1f}s ({total_duration/60:.1f} min)")

        if passed == total:
            print("\nAll formal proofs PASSED!")
        else:
            print("\nFailed/Error tests:")
            for r in self.results:
                if r.status in (TestStatus.FAIL, TestStatus.ERROR, TestStatus.TIMEOUT):
                    print(f"  - {r.name}: {r.status.value}")

        print("=" * 70)

    def list_tests(self, show_times: bool = True):
        """Print list of available tests."""
        print("\nAvailable Formal Verification Tests:")
        print("=" * 70)

        total_time = 0
        for category, tests in sorted(self.tests.items()):
            cat_time = sum(TEST_TIME_ESTIMATES.get(t, 30) for t in tests)
            total_time += cat_time
            print(f"\n{category.upper()} ({len(tests)} tests, ~{cat_time}s):")
            for test in tests:
                est = TEST_TIME_ESTIMATES.get(test, 30)
                long_marker = " [LONG]" if test in LONG_TESTS else ""
                if show_times:
                    print(f"  - {test:<30} (~{est}s){long_marker}")
                else:
                    print(f"  - {test}{long_marker}")

        print(f"\nTotal: {len(self.get_all_tests())} tests")
        if total_time >= 3600:
            print(f"Estimated total time: {total_time/3600:.1f} hours")
        else:
            print(f"Estimated total time: {total_time/60:.1f} minutes")

        long_count = sum(1 for t in self.get_all_tests() if t in LONG_TESTS)
        if long_count > 0:
            print(f"\nNote: {long_count} long-running tests can be skipped with --skip-long")


def main():
    parser = argparse.ArgumentParser(
        description="MyPC2 Formal Verification Test Runner",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python formal_runner.py                    # Run all tests
  python formal_runner.py --skip-long        # Skip tests > 60s
  python formal_runner.py -c arbiter         # Run arbiter tests only
  python formal_runner.py -t ICache2Way      # Run specific test
  python formal_runner.py -p 4               # Run in parallel
        """
    )

    parser.add_argument(
        '--category', '-c',
        help="Run tests in specific category (arbiter, cache, cpu)"
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
        help="Skip long-running tests (> 60s estimated)"
    )

    args = parser.parse_args()

    # Create runner and discover tests
    runner = FormalTestRunner()
    runner.discover_tests()

    # List tests if requested
    if args.list:
        runner.list_tests()
        return 0

    # Create results directory
    runner.create_results_directory()

    # Determine which tests to run
    if args.test:
        # Find the test
        all_tests = runner.get_all_tests()
        matching = [t for t in all_tests if args.test.lower() in t.lower()]
        if not matching:
            print(f"Test not found: {args.test}")
            return 1
        tests = matching
    elif args.category:
        tests = runner.get_tests_by_category(args.category)
        if not tests:
            print(f"No tests found in category: {args.category}")
            print(f"Available categories: {', '.join(runner.tests.keys())}")
            return 1
        # Filter long tests if requested
        if args.skip_long:
            tests = [t for t in tests if t not in LONG_TESTS]
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
    long_tests = [t for t in tests if t in LONG_TESTS]

    # Print header
    print("=" * 70)
    print("MYPC FORMAL VERIFICATION RUNNER")
    print("=" * 70)
    print(f"Tests to run: {len(tests)}")
    print(f"Estimated time: {total_estimate}")
    if long_tests:
        print(f"Long tests included: {len(long_tests)}")
        if not args.skip_long:
            print("  (use --skip-long to skip these)")
    print(f"Parallel workers: {args.parallel}")
    print(f"Results directory: {runner.results_dir}")
    print("=" * 70)
    print()

    # Run tests
    runner.run_tests(tests, parallel=args.parallel, verbose=args.verbose)

    # Print summary
    runner.print_summary()

    # Return appropriate exit code
    failed = sum(1 for r in runner.results if r.status != TestStatus.PASS)
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
