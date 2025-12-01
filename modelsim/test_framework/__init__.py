"""
Test Framework for MyPC2 Verilog Simulation Tests

This framework provides a structured way to run Icarus Verilog and Verilator
tests with proper result collection and reporting.
"""

from .results import TestResult, TestStatus, TestSuite
from .base_test import BaseTest
from .iverilog_test import IverilogTest
from .verilator_test import VerilatorTest
from .utils import find_iverilog, find_verilator, parse_test_output

__all__ = [
    'TestResult',
    'TestStatus',
    'TestSuite',
    'BaseTest',
    'IverilogTest',
    'VerilatorTest',
    'find_iverilog',
    'find_verilator',
    'parse_test_output',
]
