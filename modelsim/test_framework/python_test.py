"""
Python script test helper class.

Runs Python test scripts that return 0 on success, non-zero on failure.
"""

import os
import subprocess
from typing import List, Optional

from .base_test import BaseTest
from .utils import get_project_root


class PythonScriptTest(BaseTest):
    """
    Test class for running Python test scripts.

    This handles execution of Python scripts that return 0 on success.
    """

    # Path to the Python script (relative to project root)
    script: str = ""

    # Working directory for the script (relative to project root)
    work_dir: str = ""

    # Command-line arguments to pass to the script
    script_args: List[str] = []

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self._project_root = get_project_root()

    def setup(self):
        """Verify the script exists."""
        script_path = os.path.join(self._project_root, self.script)
        if not os.path.exists(script_path):
            raise RuntimeError(f"Script not found: {script_path}")

    def compile(self) -> bool:
        """Python scripts don't need compilation."""
        return True

    def run_simulation(self) -> tuple:
        """
        Run the Python test script.

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        script_path = os.path.join(self._project_root, self.script)

        # Determine working directory
        if self.work_dir:
            cwd = os.path.join(self._project_root, self.work_dir)
        else:
            cwd = os.path.dirname(script_path)

        # Build command
        cmd = ["python3", script_path] + list(self.script_args)

        try:
            result = subprocess.run(
                cmd,
                cwd=cwd,
                capture_output=True,
                timeout=self.timeout,
                env={**os.environ}
            )

            # Decode with error handling
            stdout = result.stdout.decode('utf-8', errors='replace')
            stderr = result.stderr.decode('utf-8', errors='replace')
            return (result.returncode, stdout, stderr)

        except subprocess.TimeoutExpired:
            raise TimeoutError(f"Script timed out after {self.timeout}s")

        except Exception as e:
            return (1, "", str(e))

    def teardown(self):
        """No cleanup needed for Python scripts."""
        pass
