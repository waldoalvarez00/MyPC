"""
Test result classes for tracking and reporting test outcomes.
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import List, Optional
import json
from datetime import datetime


class TestStatus(Enum):
    """Test execution status."""
    PASS = "pass"
    FAIL = "fail"
    SKIP = "skip"
    ERROR = "error"
    TIMEOUT = "timeout"


@dataclass
class TestResult:
    """Result of a single test execution."""
    name: str
    status: TestStatus
    duration: float = 0.0
    tests_run: int = 0
    tests_passed: int = 0
    tests_failed: int = 0
    output: str = ""
    error: str = ""
    category: str = ""
    log_file: str = ""

    @property
    def is_success(self) -> bool:
        """Check if test passed or was skipped."""
        return self.status in (TestStatus.PASS, TestStatus.SKIP)

    def to_dict(self) -> dict:
        """Convert to dictionary for JSON serialization."""
        return {
            'name': self.name,
            'status': self.status.value,
            'duration': self.duration,
            'tests_run': self.tests_run,
            'tests_passed': self.tests_passed,
            'tests_failed': self.tests_failed,
            'category': self.category,
            'log_file': self.log_file,
        }

    def summary_line(self) -> str:
        """Generate a one-line summary of the result."""
        status_icons = {
            TestStatus.PASS: "PASS",
            TestStatus.FAIL: "FAIL",
            TestStatus.SKIP: "SKIP",
            TestStatus.ERROR: "ERR ",
            TestStatus.TIMEOUT: "TIME",
        }
        icon = status_icons.get(self.status, "????")
        return f"{icon} {self.name:<40} ({self.duration:.1f}s)"


@dataclass
class TestSuite:
    """Collection of test results with aggregation."""
    name: str
    results: List[TestResult] = field(default_factory=list)
    start_time: Optional[datetime] = None
    end_time: Optional[datetime] = None

    def add_result(self, result: TestResult):
        """Add a test result to the suite."""
        self.results.append(result)

    @property
    def total(self) -> int:
        """Total number of tests run."""
        return len(self.results)

    @property
    def passed(self) -> int:
        """Number of passed tests."""
        return sum(1 for r in self.results if r.status == TestStatus.PASS)

    @property
    def failed(self) -> int:
        """Number of failed tests."""
        return sum(1 for r in self.results if r.status == TestStatus.FAIL)

    @property
    def skipped(self) -> int:
        """Number of skipped tests."""
        return sum(1 for r in self.results if r.status == TestStatus.SKIP)

    @property
    def errors(self) -> int:
        """Number of tests with errors."""
        return sum(1 for r in self.results if r.status in (TestStatus.ERROR, TestStatus.TIMEOUT))

    @property
    def pass_rate(self) -> float:
        """Pass rate as percentage."""
        if self.total == 0:
            return 0.0
        return (self.passed / self.total) * 100

    @property
    def duration(self) -> float:
        """Total duration of all tests."""
        return sum(r.duration for r in self.results)

    def get_by_status(self, status: TestStatus) -> List[TestResult]:
        """Get all results with a specific status."""
        return [r for r in self.results if r.status == status]

    def get_by_category(self, category: str) -> List[TestResult]:
        """Get all results in a specific category."""
        return [r for r in self.results if r.category == category]

    def to_dict(self) -> dict:
        """Convert to dictionary for JSON serialization."""
        return {
            'name': self.name,
            'total': self.total,
            'passed': self.passed,
            'failed': self.failed,
            'skipped': self.skipped,
            'errors': self.errors,
            'pass_rate': self.pass_rate,
            'duration': self.duration,
            'start_time': self.start_time.isoformat() if self.start_time else None,
            'end_time': self.end_time.isoformat() if self.end_time else None,
            'results': [r.to_dict() for r in self.results],
        }

    def to_json(self, indent: int = 2) -> str:
        """Convert to JSON string."""
        return json.dumps(self.to_dict(), indent=indent)

    def print_summary(self):
        """Print a summary of the test suite results."""
        print("\n" + "=" * 60)
        print(f"TEST SUITE: {self.name}")
        print("=" * 60)
        print(f"Total Tests: {self.total}")
        print(f"Passed:      {self.passed}")
        print(f"Failed:      {self.failed}")
        print(f"Skipped:     {self.skipped}")
        print(f"Errors:      {self.errors}")
        print(f"Pass Rate:   {self.pass_rate:.1f}%")
        print(f"Duration:    {self.duration:.1f}s")
        print("=" * 60)

        if self.passed > 0:
            print(f"\nPassed Tests ({self.passed}):")
            for r in self.get_by_status(TestStatus.PASS):
                print(f"  + {r.name}")

        if self.failed > 0:
            print(f"\nFailed Tests ({self.failed}):")
            for r in self.get_by_status(TestStatus.FAIL):
                print(f"  - {r.name}")

        if self.skipped > 0:
            print(f"\nSkipped Tests ({self.skipped}):")
            for r in self.get_by_status(TestStatus.SKIP):
                print(f"  o {r.name}")

        print()
