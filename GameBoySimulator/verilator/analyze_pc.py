#!/usr/bin/env python3
import sys

prev = None
with open('/tmp/test_output.txt') as f:
    for line in f:
        parts = line.split('|')
        if len(parts) > 2:
            pc = parts[1].strip()
            if pc != prev:
                print(line.strip())
                prev = pc
