"""
Base test class for all test implementations.
"""

from abc import ABC, abstractmethod
from typing import List, Optional
import os
import time

from .results import TestResult, TestStatus


class BaseTest(ABC):
    """
    Abstract base class for all tests.

    Subclasses must implement compile() and run() methods.
    """

    # Test metadata - override in subclasses
    name: str = "unnamed"
    category: str = "general"
    timeout: int = 180  # seconds
    description: str = ""

    def __init__(self, **kwargs):
        """Initialize test with optional overrides."""
        for key, value in kwargs.items():
            if hasattr(self, key):
                setattr(self, key, value)

    @abstractmethod
    def compile(self) -> bool:
        """
        Compile the test.

        Returns:
            True if compilation succeeded, False otherwise
        """
        pass

    @abstractmethod
    def run_simulation(self) -> tuple:
        """
        Run the simulation.

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        pass

    def setup(self):
        """Optional setup before test runs."""
        pass

    def teardown(self):
        """Optional cleanup after test runs."""
        pass

    def execute(self) -> TestResult:
        """
        Execute the full test lifecycle.

        Returns:
            TestResult with outcome
        """
        start_time = time.time()

        try:
            # Setup
            self.setup()

            # Compile
            if not self.compile():
                duration = time.time() - start_time
                return TestResult(
                    name=self.name,
                    status=TestStatus.SKIP,
                    duration=duration,
                    category=self.category,
                    error="Compilation failed"
                )

            # Run simulation
            exit_code, stdout, stderr = self.run_simulation()

            duration = time.time() - start_time

            # Parse results
            from .utils import parse_test_output, check_test_success, check_skip_conditions

            output = stdout + "\n" + stderr
            total, passed, failed = parse_test_output(output)

            # Determine status
            if check_skip_conditions(output):
                status = TestStatus.SKIP
            elif check_test_success(output, exit_code):
                status = TestStatus.PASS
            else:
                status = TestStatus.FAIL

            return TestResult(
                name=self.name,
                status=status,
                duration=duration,
                tests_run=total,
                tests_passed=passed,
                tests_failed=failed,
                output=stdout,
                error=stderr,
                category=self.category
            )

        except TimeoutError:
            duration = time.time() - start_time
            return TestResult(
                name=self.name,
                status=TestStatus.TIMEOUT,
                duration=duration,
                category=self.category,
                error=f"Test timed out after {self.timeout}s"
            )

        except Exception as e:
            duration = time.time() - start_time
            return TestResult(
                name=self.name,
                status=TestStatus.ERROR,
                duration=duration,
                category=self.category,
                error=str(e)
            )

        finally:
            self.teardown()

    def __repr__(self):
        return f"{self.__class__.__name__}(name={self.name!r}, category={self.category!r})"
