#!/usr/bin/env python3
"""
Script to parse shell test scripts and generate Python test configurations.

This parses all run_*.sh scripts and extracts:
- iverilog flags
- defines (-D)
- includes (-I)
- source files (.sv, .v)
- testbench file
"""

import os
import re
import glob
from typing import List, Dict, Tuple, Optional


def parse_shell_script(script_path: str) -> Optional[Dict]:
    """Parse a shell script and extract iverilog configuration."""
    with open(script_path, 'r') as f:
        content = f.read()

    # Find iverilog command
    # Look for patterns like:
    # iverilog -g2012 \
    #     -o output \
    #     ... \
    #     files...

    # First, normalize continuation lines
    content = re.sub(r'\\\s*\n\s*', ' ', content)

    # Find iverilog command
    iverilog_match = re.search(r'iverilog\s+([^|]+?)(?:\s*2>&1|\s*$)', content, re.MULTILINE)
    if not iverilog_match:
        return None

    iverilog_cmd = iverilog_match.group(1)

    # Extract flags
    defines = re.findall(r'-D(\w+(?:=\w+)?)', iverilog_cmd)
    includes = re.findall(r'-I\s*([^\s]+)', iverilog_cmd)
    top_module = re.search(r'-s\s+(\w+)', iverilog_cmd)
    top_module = top_module.group(1) if top_module else None

    # Extract source files (ending in .sv or .v)
    # Normalize paths (remove ../../ or ../)
    files = re.findall(r'([^\s]+\.(?:sv|svh|v))\b', iverilog_cmd)

    # Separate testbench from source files
    testbench = None
    sources = []

    for f in files:
        # Skip files with unresolved shell variables
        if '$' in f:
            continue

        # Normalize path
        f = f.replace('../../', '').replace('../', '')

        # Check if it's a testbench
        if 'modelsim/' in f or f.endswith('_tb.sv'):
            if f.startswith('modelsim/'):
                f = f.replace('modelsim/', '')
            testbench = f
        else:
            # Convert Quartus path to project-relative
            if f.startswith('Quartus/'):
                sources.append(f)
            else:
                sources.append(f'Quartus/rtl/{f}')

    # Normalize includes
    normalized_includes = []
    for inc in includes:
        # Skip includes with unresolved shell variables
        if '$' in inc:
            continue
        inc = inc.replace('../../', '').replace('../', '')
        if not inc.startswith('Quartus/'):
            inc = f'Quartus/rtl/{inc.lstrip("./")}'
        normalized_includes.append(inc)

    # Extract name from script
    script_name = os.path.basename(script_path)
    test_name = script_name.replace('run_', '').replace('_test.sh', '').replace('_sim.sh', '').replace('.sh', '')

    return {
        'name': test_name,
        'testbench': testbench,
        'sources': sources,
        'includes': normalized_includes,
        'defines': defines,
        'top_module': top_module,
        'script': script_name
    }


def guess_category(test_name: str, sources: List[str]) -> str:
    """Guess the test category based on name and sources."""
    name_lower = test_name.lower()
    sources_str = ' '.join(sources).lower()

    if 'fpu' in name_lower or 'fpu8087' in sources_str:
        return 'fpu'
    elif 'vga' in name_lower or 'cga' in name_lower:
        return 'video'
    elif 'uart' in name_lower:
        return 'serial'
    elif 'ps2' in name_lower or 'keyboard' in name_lower or 'mouse' in name_lower:
        return 'input'
    elif 'dma' in name_lower and 'arbiter' not in name_lower:
        return 'dma'
    elif 'floppy' in name_lower:
        return 'floppy'
    elif 'pic' in name_lower or '8259' in name_lower or 'ppi' in name_lower or 'timer' in name_lower or '8253' in name_lower:
        return 'peripheral'
    elif 'cache' in name_lower or 'sdram' in name_lower or 'fifo' in name_lower:
        return 'memory'
    elif 'arbiter' in name_lower:
        return 'arbiter'
    elif 'bios' in name_lower:
        return 'bios'
    elif 'audio' in name_lower or 'speaker' in name_lower:
        return 'audio'
    else:
        return 'core'


def generate_config_file(configs: List[Dict], output_path: str):
    """Generate a Python configuration file from parsed configs."""

    with open(output_path, 'w') as f:
        f.write('"""')
        f.write('''
Test configurations for MyPC2 Verilog test suite.

Auto-generated from shell scripts by generate_test_configs.py
''')
        f.write('"""')
        f.write('\n\n')
        f.write('from typing import List, Dict, Optional\n\n')

        # Write TestConfig class
        f.write('''
class TestConfig:
    """Configuration for a single Verilog test."""

    def __init__(
        self,
        name: str,
        testbench: str,
        sources: List[str],
        includes: Optional[List[str]] = None,
        defines: Optional[List[str]] = None,
        top_module: Optional[str] = None,
        category: str = "core",
        timeout: int = 120,
        description: str = ""
    ):
        self.name = name
        self.testbench = testbench
        self.sources = sources
        self.includes = includes or []
        self.defines = defines or []
        self.top_module = top_module
        self.category = category
        self.timeout = timeout
        self.description = description


# =============================================================================
# Test Configurations
# =============================================================================

TEST_CONFIGS: Dict[str, TestConfig] = {}

''')

        # Group by category
        by_category = {}
        for config in configs:
            cat = config.get('category', 'core')
            if cat not in by_category:
                by_category[cat] = []
            by_category[cat].append(config)

        # Write configs by category
        for category in sorted(by_category.keys()):
            f.write(f'\n# {"=" * 77}\n')
            f.write(f'# {category.upper()} Tests\n')
            f.write(f'# {"=" * 77}\n\n')

            for config in sorted(by_category[category], key=lambda x: x['name']):
                name = config['name']
                testbench = config.get('testbench', '')
                sources = config.get('sources', [])
                includes = config.get('includes', [])
                defines = config.get('defines', [])
                top_module = config.get('top_module')

                f.write(f'TEST_CONFIGS["{name}"] = TestConfig(\n')
                f.write(f'    name="{name}",\n')
                f.write(f'    testbench="{testbench}",\n')

                # Sources
                f.write('    sources=[\n')
                for src in sources:
                    f.write(f'        "{src}",\n')
                f.write('    ],\n')

                # Includes
                if includes:
                    f.write('    includes=[\n')
                    for inc in includes:
                        f.write(f'        "{inc}",\n')
                    f.write('    ],\n')
                else:
                    f.write('    includes=[],\n')

                # Defines
                if defines:
                    f.write(f'    defines={defines},\n')

                # Top module
                if top_module:
                    f.write(f'    top_module="{top_module}",\n')

                f.write(f'    category="{category}",\n')
                f.write(f'    description="{name} tests"\n')
                f.write(')\n\n')

        # Write helper functions
        f.write('''
# =============================================================================
# Helper Functions
# =============================================================================

def get_all_tests() -> List[TestConfig]:
    """Return all test configurations."""
    return list(TEST_CONFIGS.values())


def get_tests_by_category(category: str) -> List[TestConfig]:
    """Return tests filtered by category."""
    return [t for t in TEST_CONFIGS.values() if t.category == category]


def get_test_by_name(name: str) -> Optional[TestConfig]:
    """Return a specific test by name."""
    return TEST_CONFIGS.get(name)


def get_all_categories() -> List[str]:
    """Return list of all test categories."""
    return list(set(t.category for t in TEST_CONFIGS.values()))
''')


def main():
    """Parse all shell scripts and generate configurations."""
    modelsim_dir = os.path.dirname(os.path.abspath(__file__))

    # Find all test scripts
    scripts = glob.glob(os.path.join(modelsim_dir, 'run_*_test.sh'))
    scripts.extend(glob.glob(os.path.join(modelsim_dir, 'run_*_sim.sh')))

    # Parse each script
    configs = []
    skipped = []

    for script in sorted(scripts):
        config = parse_shell_script(script)
        if config:
            # Guess category
            config['category'] = guess_category(config['name'], config['sources'])
            configs.append(config)
            print(f"Parsed: {os.path.basename(script)} -> {config['name']} ({config['category']})")
        else:
            skipped.append(script)
            print(f"Skipped: {os.path.basename(script)} (no iverilog command found)")

    # Generate output file
    output_path = os.path.join(modelsim_dir, 'test_configs_generated.py')
    generate_config_file(configs, output_path)

    print(f"\nGenerated {len(configs)} test configurations")
    print(f"Skipped {len(skipped)} scripts")
    print(f"Output: {output_path}")

    # Summary by category
    print("\nBy category:")
    by_cat = {}
    for c in configs:
        cat = c['category']
        by_cat[cat] = by_cat.get(cat, 0) + 1
    for cat, count in sorted(by_cat.items()):
        print(f"  {cat}: {count}")


if __name__ == '__main__':
    main()
