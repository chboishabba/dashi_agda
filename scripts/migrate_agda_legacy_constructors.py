#!/usr/bin/env python3
"""
migrate_agda_legacy_constructors.py

Safely migrate legacy Agda constructor syntax of the form:

    data Foo : Set where
      a
      b
      : Foo

to:

    data Foo : Set where
      a : Foo
      b : Foo

This script uses a linear line-by-line parser with strict boundary and
indentation validation. It is completely deterministic, runs in O(N) linear time,
and performs zero multiline regular expressions or backtracking.

Safety rules:
  - Only scans .agda files.
  - Matches `data <Name> ... where` header lines.
  - Requires all constructor lines to share exact indentation > header indentation.
  - Requires trailing signature line `: <Name>` at that exact indentation.
  - Rejects definitions containing `=`, `->`, `\`, comments within constructors,
    nested declarations, or conflicting layout.
  - Preserves exact source bytes, newlines, and surrounding formatting.
"""

from __future__ import annotations

import argparse
import difflib
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator, Sequence


@dataclass(frozen=True)
class Edit:
    start_line: int
    end_line: int
    replacement_lines: list[bytes]


def strip_line_ending(line: bytes) -> tuple[bytes, bytes]:
    if line.endswith(b"\r\n"):
        return line[:-2], b"\r\n"
    if line.endswith(b"\n"):
        return line[:-1], b"\n"
    if line.endswith(b"\r"):
        return line[:-1], b"\r"
    return line, b""


def leading_ws(line: bytes) -> bytes:
    return line[: len(line) - len(line.lstrip(b" \t"))]


def is_simple_constructor_name(s: bytes) -> bool:
    if not s or s.startswith(b"--") or b":" in s or b"=" in s or b"->" in s or b"\\" in s:
        return False
    forbidden_prefixes = (
        b"data ", b"record ", b"module ", b"open ", b"import ", b"private ",
        b"public ", b"abstract ", b"instance ", b"macro ", b"mutual ",
        b"variable ", b"field ", b"postulate ", b"primitive ", b"{-#"
    )
    return not s.startswith(forbidden_prefixes)


def migrate_file_lines(lines: list[bytes]) -> list[bytes] | None:
    i = 0
    n = len(lines)
    changed = False
    out: list[bytes] = []

    while i < n:
        line = lines[i]
        body, ending = strip_line_ending(line)
        stripped = body.strip()

        # Check for data declaration header ending with `where`
        if stripped.startswith(b"data ") and stripped.endswith(b"where") and b":" in stripped:
            # Extract data type name: between "data " and ":"
            after_data = stripped[5:].lstrip()
            type_name = after_data.split()[0].split(b":")[0].strip()
            header_indent = leading_ws(body)

            # Look ahead for constructor lines and trailing `: <type_name>`
            j = i + 1
            ctor_lines: list[tuple[int, bytes, bytes]] = []  # (index, ctor_name, ending)
            found_sig = False
            expected_sig = b": " + type_name
            target_indent = None

            while j < n:
                cur_body, cur_ending = strip_line_ending(lines[j])
                cur_stripped = cur_body.strip()

                if not cur_stripped or cur_stripped.startswith(b"--"):
                    # Blank or comment line inside data block: keep or break if not started
                    if not ctor_lines:
                        break
                    # Blank line during constructor collection: stop data block search safely
                    break

                cur_indent = leading_ws(cur_body)
                if len(cur_indent) <= len(header_indent):
                    # Dedented or same indentation: block ended without trailing signature
                    break

                if target_indent is None:
                    target_indent = cur_indent
                elif cur_indent != target_indent:
                    # Inconsistent indentation: skip safely
                    break

                # Check if this line is the trailing signature `: TypeName`
                if cur_stripped == expected_sig:
                    found_sig = True
                    break

                # Otherwise must be simple constructor name
                if is_simple_constructor_name(cur_stripped):
                    ctor_lines.append((j, cur_stripped, cur_ending))
                    j += 1
                else:
                    break

            if found_sig and ctor_lines:
                # Valid candidate! Apply migration
                out.append(line)
                for _, ctor, c_ending in ctor_lines:
                    out.append(target_indent + ctor + b" : " + type_name + c_ending)
                out.append(strip_line_ending(lines[j])[1])  # preserve trailing signature newline
                i = j + 1
                changed = True
                continue

        out.append(line)
        i += 1

    return out if changed else None


def iter_agda_files(paths: Sequence[Path]) -> Iterator[Path]:
    seen: set[Path] = set()
    for p in paths:
        if p.is_file():
            if p.suffix == ".agda":
                rp = p.resolve()
                if rp not in seen:
                    seen.add(rp)
                    yield p
            continue
        if p.is_dir():
            for f in sorted(p.rglob("*.agda")):
                if any(part in {".git", ".cache", ".venv", "dist", "build"} for part in f.parts):
                    continue
                rp = f.resolve()
                if rp not in seen:
                    seen.add(rp)
                    yield f


def print_diff(path: Path, before: list[bytes], after: list[bytes]) -> None:
    before_text = [l.decode("utf-8", errors="surrogateescape") for l in before]
    after_text = [l.decode("utf-8", errors="surrogateescape") for l in after]
    sys.stdout.writelines(
        difflib.unified_diff(
            before_text,
            after_text,
            fromfile=str(path),
            tofile=str(path),
        )
    )


def main(argv: Sequence[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Migrate legacy Agda trailing constructor signatures safely in linear time."
    )
    ap.add_argument("paths", nargs="+", type=Path, help="Agda files or directories to inspect")
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="report candidates; exit 1 if any file would change")
    mode.add_argument("--diff", action="store_true", help="print unified diffs; do not modify files")
    mode.add_argument("--write", action="store_true", help="apply safe rewrites in place")
    args = ap.parse_args(argv)

    files = list(iter_agda_files(args.paths))
    if not files:
        print("error: no .agda files found", file=sys.stderr)
        return 2

    changed_files = 0
    for path in files:
        try:
            before = path.read_bytes().splitlines(keepends=True)
            after = migrate_file_lines(before)
        except OSError as exc:
            print(f"error: {path}: {exc}", file=sys.stderr)
            return 2

        if after is None:
            continue

        changed_files += 1
        if args.check:
            print(f"would-change {path}")
        elif args.diff:
            print_diff(path, before, after)
        elif args.write:
            path.write_bytes(b"".join(after))
            print(f"updated {path}")

    print(f"\nscanned={len(files)} changed_files={changed_files}", file=sys.stderr)
    if args.check and changed_files:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
