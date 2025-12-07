"""
Icarus Verilog test helper class.
"""

import os
import subprocess
import tempfile
from typing import List, Optional

from .base_test import BaseTest
from .utils import find_iverilog, find_vvp, get_project_root, get_modelsim_dir


class IverilogTest(BaseTest):
    """
    Test class for Icarus Verilog simulations.

    This handles compilation with iverilog and execution with vvp.
    """

    # Source files to compile (relative to project root)
    sources: List[str] = []

    # Testbench file (relative to modelsim directory)
    testbench: str = ""

    # Include directories (relative to project root)
    includes: List[str] = []

    # Preprocessor defines (e.g., ["ICARUS", "CACHE_LINES=512"])
    defines: List[str] = []

    # Top module name (optional, for -s flag)
    top_module: Optional[str] = None

    # Additional iverilog flags
    iverilog_flags: List[str] = ["-g2012"]

    # Output file name (will be generated if not set)
    output_file: str = ""

    # Working directory for compilation
    work_dir: str = ""

    def __init__(self, **kwargs):
        super().__init__(**kwargs)

        # Set default output file if not specified
        if not self.output_file:
            self.output_file = f"{self.name}_sim"

        # Set default work directory
        if not self.work_dir:
            self.work_dir = get_modelsim_dir()

        # Store paths
        self._project_root = get_project_root()
        self._iverilog = None
        self._vvp = None
        self._compiled_output = None

    def setup(self):
        """Find tools and prepare for compilation."""
        self._iverilog = find_iverilog()
        self._vvp = find_vvp()

        if not self._iverilog:
            raise RuntimeError("iverilog not found. Please install Icarus Verilog.")
        if not self._vvp:
            raise RuntimeError("vvp not found. Please install Icarus Verilog.")

    def compile(self) -> bool:
        """
        Compile the test with iverilog.

        Returns:
            True if compilation succeeded
        """
        # Build command
        cmd = [self._iverilog]
        cmd.extend(self.iverilog_flags)

        # Add preprocessor defines
        for define in self.defines:
            cmd.append(f"-D{define}")

        # Add top module if specified
        if self.top_module:
            cmd.extend(["-s", self.top_module])

        # Add include directories
        for inc in self.includes:
            inc_path = os.path.join(self._project_root, inc)
            cmd.extend(["-I", inc_path])

        # Set output file
        self._compiled_output = os.path.join(self.work_dir, self.output_file)
        cmd.extend(["-o", self._compiled_output])

        # Add testbench
        if self.testbench:
            tb_path = os.path.join(get_modelsim_dir(), self.testbench)
            cmd.append(tb_path)

        # Add source files
        for src in self.sources:
            src_path = os.path.join(self._project_root, src)
            cmd.append(src_path)

        # Run compilation
        try:
            result = subprocess.run(
                cmd,
                cwd=self.work_dir,
                capture_output=True,
                timeout=60
            )

            if result.returncode != 0:
                print(f"Compilation failed for {self.name}:")
                print(result.stderr.decode('utf-8', errors='replace'))
                return False

            return True

        except subprocess.TimeoutExpired:
            print(f"Compilation timed out for {self.name}")
            return False

        except Exception as e:
            print(f"Compilation error for {self.name}: {e}")
            return False

    def run_simulation(self) -> tuple:
        """
        Run the simulation with vvp.

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        if not self._compiled_output or not os.path.exists(self._compiled_output):
            return (1, "", "Compiled output not found")

        cmd = [self._vvp, self._compiled_output]

        try:
            result = subprocess.run(
                cmd,
                cwd=self.work_dir,
                capture_output=True,
                timeout=self.timeout
            )

            # Decode with error handling for binary output
            stdout = result.stdout.decode('utf-8', errors='replace')
            stderr = result.stderr.decode('utf-8', errors='replace')
            return (result.returncode, stdout, stderr)

        except subprocess.TimeoutExpired:
            raise TimeoutError(f"Simulation timed out after {self.timeout}s")

        except Exception as e:
            return (1, "", str(e))

    def teardown(self):
        """Clean up compiled files."""
        if self._compiled_output and os.path.exists(self._compiled_output):
            try:
                os.remove(self._compiled_output)
            except OSError:
                pass
