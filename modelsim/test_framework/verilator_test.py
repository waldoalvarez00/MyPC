"""
Verilator test helper class.
"""

import os
import subprocess
from typing import List

from .base_test import BaseTest
from .utils import find_verilator, get_project_root, get_modelsim_dir


class VerilatorTest(BaseTest):
    """
    Test class for Verilator simulations.

    This handles compilation with verilator and execution of the resulting binary.
    """

    # Source files to compile (relative to project root)
    sources: List[str] = []

    # C++ testbench file (relative to modelsim directory)
    cpp_testbench: str = ""

    # Top module name
    top_module: str = ""

    # Include directories (relative to project root)
    includes: List[str] = []

    # Additional verilator flags
    verilator_flags: List[str] = [
        "--cc", "--exe", "--build", "-Wall",
        "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC", "-Wno-UNUSEDSIGNAL",
        "-Wno-CASEINCOMPLETE", "-Wno-PINCONNECTEMPTY",
        "--trace"  # Enable VCD tracing (required by testbenches using VerilatedVcdC)
    ]

    # Output directory for Verilator
    obj_dir: str = "obj_dir"

    # Enable code coverage (line + toggle)
    enable_coverage: bool = False

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self._project_root = get_project_root()
        self._modelsim_dir = get_modelsim_dir()
        self._verilator = None
        self._binary_path = None

    def setup(self):
        """Find Verilator and prepare environment."""
        self._verilator = find_verilator()

        if not self._verilator:
            raise RuntimeError("verilator not found. Please install Verilator.")

        # Set up environment for Verilator
        verilator_root = "/tmp/verilator_extract/usr/share/verilator"
        if os.path.exists(verilator_root):
            os.environ["VERILATOR_ROOT"] = verilator_root

        # Clean previous build
        obj_path = os.path.join(self._modelsim_dir, self.obj_dir)
        if os.path.exists(obj_path):
            import shutil
            shutil.rmtree(obj_path)

    def compile(self) -> bool:
        """
        Compile with Verilator.

        Returns:
            True if compilation succeeded
        """
        # Build command
        cmd = [self._verilator]
        cmd.extend(self.verilator_flags)

        # Add coverage flags if enabled
        if self.enable_coverage:
            cmd.extend(['--coverage', '--coverage-line', '--coverage-toggle'])

        # Add include directories
        for inc in self.includes:
            inc_path = os.path.join(self._project_root, inc)
            cmd.append(f"-I{inc_path}")

        # Set top module
        if self.top_module:
            cmd.extend(["--top-module", self.top_module])

        # Add source files
        for src in self.sources:
            src_path = os.path.join(self._project_root, src)
            cmd.append(src_path)

        # Add C++ testbench
        if self.cpp_testbench:
            cpp_path = os.path.join(self._modelsim_dir, self.cpp_testbench)
            cmd.append(cpp_path)

        # Run Verilator
        try:
            result = subprocess.run(
                cmd,
                cwd=self._modelsim_dir,
                capture_output=True,
                text=True,
                timeout=120
            )

            if result.returncode != 0:
                print(f"Verilator compilation failed for {self.name}:")
                print(result.stderr)
                return False

            # Determine binary path
            binary_name = f"V{self.top_module}" if self.top_module else "Vtop"
            self._binary_path = os.path.join(
                self._modelsim_dir, self.obj_dir, binary_name
            )

            return os.path.exists(self._binary_path)

        except subprocess.TimeoutExpired:
            print(f"Verilator compilation timed out for {self.name}")
            return False

        except Exception as e:
            print(f"Verilator error for {self.name}: {e}")
            return False

    def run_simulation(self) -> tuple:
        """
        Run the compiled Verilator binary.

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        if not self._binary_path or not os.path.exists(self._binary_path):
            return (1, "", "Compiled binary not found")

        try:
            result = subprocess.run(
                [self._binary_path],
                cwd=self._modelsim_dir,
                capture_output=True,
                text=True,
                timeout=self.timeout
            )

            return (result.returncode, result.stdout, result.stderr)

        except subprocess.TimeoutExpired:
            raise TimeoutError(f"Simulation timed out after {self.timeout}s")

        except Exception as e:
            return (1, "", str(e))

    def teardown(self):
        """Clean up build directory."""
        obj_path = os.path.join(self._modelsim_dir, self.obj_dir)
        if os.path.exists(obj_path):
            import shutil
            try:
                shutil.rmtree(obj_path)
            except OSError:
                pass
