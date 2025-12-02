#!/usr/bin/env python3
"""
RTL Test Coverage Analyzer

Scans RTL directories and compares against existing testbenches
to identify coverage gaps.

Usage:
    python3 analyze_coverage.py           # Analyze module coverage gaps
    python3 analyze_coverage.py --json    # Output as JSON for CI/CD
    python3 analyze_coverage.py --report  # Generate HTML coverage report
    python3 analyze_coverage.py --clean   # Remove coverage artifacts
"""

import os
import glob
import shutil
from pathlib import Path
from collections import defaultdict
from test_configs import TEST_CONFIGS

# RTL directories to scan
RTL_DIRS = {
    'cpu': 'Quartus/rtl/CPU',
    'cpu_alu': 'Quartus/rtl/CPU/alu',
    'cpu_cdc': 'Quartus/rtl/CPU/cdc',
    'common': 'Quartus/rtl/common',
    'fpu': 'Quartus/rtl/FPU8087',
    'vga': 'Quartus/rtl/VGA',
    'cga': 'Quartus/rtl/CGA',
    'kf8253': 'Quartus/rtl/KF8253',
    'kf8255': 'Quartus/rtl/KF8255',
    'kf8259': 'Quartus/rtl/KF8259',
    'kf8237': 'Quartus/rtl/KF8237-DMA',
    'uart': 'Quartus/rtl/uart',
    'ps2': 'Quartus/rtl/ps2',
    'floppy': 'Quartus/rtl/Floppy',
    'keyboard': 'Quartus/rtl/Keyboard',
    'bios': 'Quartus/rtl/bios',
    'sdram': 'Quartus/rtl/sdram',
    'audio': 'Quartus/rtl/audio',
}


def get_rtl_modules():
    """Scan RTL directories and return dict of category -> [modules]"""
    modules = defaultdict(list)
    for category, path in RTL_DIRS.items():
        full_path = Path('..') / path
        if full_path.exists():
            for ext in ['*.sv', '*.v']:
                for f in full_path.glob(ext):
                    if '_tb' not in f.name.lower() and 'test' not in f.name.lower():
                        modules[category].append(f.stem)
    return modules


def get_tested_modules():
    """Extract modules covered by existing tests from test_configs"""
    tested = set()
    for config in TEST_CONFIGS.values():
        for source in config.sources:
            # Extract module name from path
            module = Path(source).stem
            tested.add(module.lower())
    return tested


def analyze_gaps():
    """Main analysis function"""
    rtl_modules = get_rtl_modules()
    tested = get_tested_modules()

    report = {
        'total_modules': 0,
        'tested_modules': 0,
        'untested_modules': 0,
        'by_category': {},
    }

    for category, modules in sorted(rtl_modules.items()):
        cat_tested = []
        cat_untested = []
        for mod in modules:
            if mod.lower() in tested:
                cat_tested.append(mod)
            else:
                cat_untested.append(mod)

        report['by_category'][category] = {
            'total': len(modules),
            'tested': cat_tested,
            'untested': cat_untested,
            'coverage_pct': len(cat_tested) / len(modules) * 100 if modules else 0
        }
        report['total_modules'] += len(modules)
        report['tested_modules'] += len(cat_tested)

    report['untested_modules'] = report['total_modules'] - report['tested_modules']
    report['coverage_pct'] = report['tested_modules'] / report['total_modules'] * 100 if report['total_modules'] > 0 else 0

    return report


def print_report(report):
    """Print formatted coverage report"""
    print("=" * 70)
    print("RTL TEST COVERAGE ANALYSIS")
    print("=" * 70)
    print(f"\nOverall: {report['tested_modules']}/{report['total_modules']} modules tested ({report['coverage_pct']:.1f}%)")
    print(f"Gaps: {report['untested_modules']} modules without testbenches\n")

    print("-" * 70)
    print(f"{'Category':<15} {'Tested':<10} {'Total':<10} {'Coverage':<10} {'Status'}")
    print("-" * 70)

    for cat, data in sorted(report['by_category'].items(), key=lambda x: x[1]['coverage_pct']):
        status = "OK" if data['coverage_pct'] >= 50 else "GAP" if data['coverage_pct'] > 0 else "NONE"
        print(f"{cat:<15} {len(data['tested']):<10} {data['total']:<10} {data['coverage_pct']:>6.1f}%    {status}")

    print("\n" + "=" * 70)
    print("PRIORITY GAPS (0% coverage)")
    print("=" * 70)
    for cat, data in report['by_category'].items():
        if data['coverage_pct'] == 0 and data['untested']:
            print(f"\n{cat}: {', '.join(data['untested'][:5])}{'...' if len(data['untested']) > 5 else ''}")


def generate_coverage_report(output_dir='coverage_report'):
    """Generate HTML coverage report from Verilator tests"""
    import subprocess

    # Run verilator tests with coverage
    verilator_tests = [name for name, cfg in TEST_CONFIGS.items()
                       if cfg.simulator == 'verilator']

    if not verilator_tests:
        print("No Verilator tests found. Verilator code coverage not available.")
        return

    coverage_files = []
    for test in verilator_tests:
        # Run test and collect coverage.dat
        print(f"Running {test} with coverage...")
        result = subprocess.run(
            ['python3', 'test_runner.py', '--test', test],
            capture_output=True,
            text=True
        )
        cov_file = f'test_results_*/obj_dir_{test}/coverage.dat'
        coverage_files.extend(glob.glob(cov_file))

    # Merge coverage files
    if coverage_files:
        subprocess.run([
            'verilator_coverage', '--annotate', output_dir,
            '--annotate-all', *coverage_files
        ])
        print(f"Coverage report generated in {output_dir}/")
    else:
        print("No coverage data files found. Run tests with --coverage first.")


def cleanup_coverage_artifacts():
    """Remove all coverage analysis artifacts"""
    artifacts = [
        'coverage_report',           # Generated HTML reports
        'coverage.dat',              # Verilator coverage data
    ]

    # Glob patterns for coverage files in test results
    glob_patterns = [
        'test_results_*/obj_dir_*/coverage.dat',
        'test_results_*/*.dat',
        '*_coverage.json',
    ]

    removed = []

    # Remove fixed artifacts
    for artifact in artifacts:
        path = Path(artifact)
        if path.exists():
            if path.is_dir():
                shutil.rmtree(path)
            else:
                path.unlink()
            removed.append(str(path))

    # Remove glob-matched files
    for pattern in glob_patterns:
        for match in glob.glob(pattern, recursive=True):
            path = Path(match)
            if path.exists():
                path.unlink()
                removed.append(str(path))

    if removed:
        print(f"Cleaned up {len(removed)} coverage artifact(s):")
        for item in removed:
            print(f"  - {item}")
    else:
        print("No coverage artifacts found to clean up.")

    return removed


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description='RTL Test Coverage Analyzer')
    parser.add_argument('--report', action='store_true',
                        help='Generate HTML coverage report from Verilator tests')
    parser.add_argument('--clean', action='store_true',
                        help='Remove all coverage analysis artifacts')
    parser.add_argument('--json', action='store_true',
                        help='Output results as JSON for CI/CD integration')
    args = parser.parse_args()

    if args.clean:
        cleanup_coverage_artifacts()
    elif args.report:
        generate_coverage_report()
    else:
        report = analyze_gaps()
        if args.json:
            import json
            print(json.dumps(report, indent=2))
        else:
            print_report(report)
