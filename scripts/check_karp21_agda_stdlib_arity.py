#!/usr/bin/env python3
"""Flag misplaced explicit arguments to Agda stdlib length-++.

The standard-library Data.List.Properties declaration is:

    length-++ : ∀ (xs : List A) {ys} →
                length (xs ++ ys) ≡ length xs + length ys

Therefore ListP.length-++ (xs) (ys) supplies an extra positional
argument and fails typechecking. Use length-++ (xs) {ys = ys},
or let Agda infer ys. This is not a kernel typechecking substitute.

Historical owner: Agda standard-library maintainers.
DASHI referee: scripts/referee_karp21_maxcut.sh.
"""
from __future__ import annotations
import argparse
import pathlib
import sys

NAME = "ListP.length-++"


def skip_spaces(src: str, at: int) -> int:
    while at < len(src) and src[at].isspace():
        at += 1
    return at


def skip_group(src: str, at: int) -> int:
    if at >= len(src) or src[at] != "(":
        return at
    depth = 0
    while at < len(src):
        if src[at] == "(":
            depth += 1
        elif src[at] == ")":
            depth -= 1
            if depth == 0:
                return at + 1
        at += 1
    raise ValueError("unbalanced parenthesized argument")


def positional_second_args(src: str):
    cursor = 0
    while (at := src.find(NAME, cursor)) >= 0:
        cursor = at + len(NAME)
        if src[cursor:cursor + 1] == "-":
            continue  # another lemma: length-++-suc or length-++-comm
        next_at = skip_spaces(src, cursor)
        if next_at >= len(src) or src[next_at] != "(":
            continue
        after_first = skip_spaces(src, skip_group(src, next_at))
        # Braced ys is the expected syntax for an implicit argument.
        if src[after_first:after_first + 1] == "(":
            yield src.count("\n", 0, at) + 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--repo-root", type=pathlib.Path,
        default=pathlib.Path(__file__).resolve().parents[1]
    )
    args = ap.parse_args()
    root = args.repo_root
    findings = []
    for file in sorted((root / "DASHI" / "Mathematics" / "Complexity")
                       .glob("Karp21*.agda")):
        source = file.read_text(encoding="utf-8")
        for line in positional_second_args(source):
            findings.append(f"{file.relative_to(root)}:{line}")
    for item in findings:
        print("INVALID EXPLICIT SECOND length-++ ARG:", item)
    print(
        f"Checked Karp21 Agda files; positional length-++ arity "
        f"findings: {len(findings)}."
    )
    print("This is a narrow static preflight, NOT an Agda kernel check.")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
