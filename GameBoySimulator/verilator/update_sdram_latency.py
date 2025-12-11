#!/usr/bin/env python3
"""
Update all GameBoy test files to use realistic SDRAM latency (CAS=2)
"""

import re
import sys

def update_file(filename):
    """Add cas_latency = 2 after MisterSDRAMModel creation if not already present"""

    with open(filename, 'r') as f:
        content = f.read()

    # Check if already has cas_latency = 2
    if 'cas_latency = 2' in content or 'cas_latency=2' in content:
        return False, "Already has cas_latency = 2"

    # Check if file uses MisterSDRAMModel
    if 'MisterSDRAMModel' not in content:
        return False, "Does not use MisterSDRAMModel"

    original_content = content
    modified = False

    # Pattern 1: new MisterSDRAMModel(...); with optional inline comment, followed by newline
    # Add cas_latency after the creation
    pattern1 = r'(MisterSDRAMModel\*\s+sdram\s*=\s*new\s+MisterSDRAMModel\([^)]*\);[^\n]*)\n'
    if re.search(pattern1, content):
        replacement = r'\1\n    sdram->cas_latency = 2;  // Realistic CAS latency\n'
        content = re.sub(pattern1, replacement, content)
        modified = True

    # Pattern 2: If debug line exists right after, insert before it (redundant now but keep for safety)
    pattern2 = r'(MisterSDRAMModel\*\s+sdram\s*=\s*new\s+MisterSDRAMModel\([^)]*\);[^\n]*)\n(\s+sdram->debug)'
    if not modified and re.search(pattern2, content):
        replacement = r'\1\n    sdram->cas_latency = 2;  // Realistic CAS latency\n\2'
        content = re.sub(pattern2, replacement, content)
        modified = True

    # Pattern 3: Assignment to existing pointer: sdram = new MisterSDRAMModel(...)
    pattern3 = r'(\s+sdram\s*=\s*new\s+MisterSDRAMModel\([^)]*\);[^\n]*)\n'
    if not modified and re.search(pattern3, content):
        replacement = r'\1\n    sdram->cas_latency = 2;  // Realistic CAS latency\n'
        content = re.sub(pattern3, replacement, content)
        modified = True

    if modified and content != original_content:
        with open(filename, 'w') as f:
            f.write(content)
        return True, "Updated"

    return False, "No pattern matched"

def main():
    # Read list of files from stdin or command line
    if len(sys.argv) > 1:
        files = sys.argv[1:]
    else:
        files = [line.strip() for line in sys.stdin]

    updated_count = 0
    skipped_count = 0

    for filename in files:
        if not filename:
            continue
        success, message = update_file(filename)
        if success:
            print(f"✓ {filename}: {message}")
            updated_count += 1
        else:
            print(f"- {filename}: {message}")
            skipped_count += 1

    print(f"\nSummary: Updated {updated_count} files, Skipped {skipped_count} files")

if __name__ == "__main__":
    main()
