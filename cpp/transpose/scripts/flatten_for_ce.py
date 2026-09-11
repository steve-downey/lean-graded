#!/usr/bin/env python3
"""Flatten a beman.transpose example into a single file for Compiler Explorer.

Inlines all #include <beman/transpose/...> headers recursively, leaves standard
library includes untouched, and adds comment markers showing provenance.

Usage:
    ./scripts/flatten_for_ce.py examples/simd_example.cpp > /tmp/ce_simd.cpp
    ./scripts/flatten_for_ce.py examples/soa_aos_example.cpp -o /tmp/ce_soa.cpp
"""

import argparse
import re
import sys
from pathlib import Path

INCLUDE_DIR = Path(__file__).resolve().parent.parent / "include"

BEMAN_INCLUDE_RE = re.compile(r'^\s*#include\s+<(beman/transpose/[^>]+)>\s*$')
IFNDEF_RE = re.compile(r'^\s*#ifndef\s+(\S+)\s*$')
DEFINE_RE = re.compile(r'^\s*#define\s+(\S+)\s+1?\s*$')
ENDIF_RE = re.compile(r'^\s*#endif\b')
SPDX_RE = re.compile(r'^\s*//\s*SPDX-License-Identifier:')
MODE_LINE_RE = re.compile(r'-\*-.*-\*-')


def flatten(filepath: Path, seen: set[str], depth: int = 0) -> list[str]:
    """Recursively flatten a file, inlining beman includes."""
    rel = filepath.relative_to(INCLUDE_DIR) if filepath.is_relative_to(INCLUDE_DIR) else filepath
    key = str(rel)

    if key in seen:
        return [f"// [{rel} already included above]"]
    seen.add(key)

    lines = filepath.read_text().splitlines()
    out: list[str] = []

    # Skip include guards and the first comment block for inlined headers
    i = 0
    is_header = filepath.suffix in ('.hpp', '.h')
    guard_symbol = None

    if is_header and depth > 0:
        # Skip leading comment block
        while i < len(lines) and (lines[i].startswith('//') or lines[i].strip() == ''):
            i += 1
        # Skip #ifndef GUARD / #define GUARD
        if i < len(lines) and (m := IFNDEF_RE.match(lines[i])):
            guard_symbol = m.group(1)
            i += 1
            if i < len(lines) and DEFINE_RE.match(lines[i]):
                i += 1

    while i < len(lines):
        line = lines[i]

        # Skip trailing #endif for the include guard
        if guard_symbol and ENDIF_RE.match(line) and i >= len(lines) - 2:
            remaining = [l.strip() for l in lines[i:] if l.strip()]
            if all(ENDIF_RE.match(l) or l.startswith('//') for l in remaining):
                break

        m = BEMAN_INCLUDE_RE.match(line)
        if m:
            header_path = INCLUDE_DIR / m.group(1)
            if header_path.exists():
                rel_header = m.group(1)
                out.append(f"// ┌── {rel_header} ──")
                out.extend(flatten(header_path, seen, depth + 1))
                out.append(f"// └── {rel_header} ──")
            else:
                out.append(line)
        else:
            out.append(line)

        i += 1

    return out


def collect_std_includes(lines: list[str]) -> tuple[list[str], list[str]]:
    """Hoist standard library includes to the top, deduplicated."""
    std_include_re = re.compile(r'^\s*#include\s+<([^>]+)>\s*$')
    std_includes: list[str] = []
    seen_std: set[str] = set()
    body: list[str] = []

    for line in lines:
        m = std_include_re.match(line)
        if m and not m.group(1).startswith('beman/'):
            header = m.group(1)
            if header not in seen_std:
                seen_std.add(header)
                std_includes.append(f"#include <{header}>")
        else:
            body.append(line)

    return std_includes, body


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("source", type=Path, help="Example .cpp file to flatten")
    parser.add_argument("-o", "--output", type=Path, help="Output file (default: stdout)")
    parser.add_argument("--no-hoist", action="store_true",
                        help="Don't hoist std includes to top")
    args = parser.parse_args()

    source = args.source.resolve()
    if not source.exists():
        sys.exit(f"error: {args.source} not found")

    seen: set[str] = set()
    flattened = flatten(source, seen, depth=0)

    if not args.no_hoist:
        std_includes, body = collect_std_includes(flattened)
        # Remove blank lines at top of body
        while body and body[0].strip() == '':
            body.pop(0)
        result = std_includes + [''] + body
    else:
        result = flattened

    # Collapse runs of 3+ blank lines
    output_lines: list[str] = []
    blank_count = 0
    for line in result:
        if line.strip() == '':
            blank_count += 1
            if blank_count <= 2:
                output_lines.append(line)
        else:
            blank_count = 0
            output_lines.append(line)

    text = '\n'.join(output_lines) + '\n'

    if args.output:
        args.output.write_text(text)
        print(f"Written to {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
