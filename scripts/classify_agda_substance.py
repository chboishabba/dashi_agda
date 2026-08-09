#!/usr/bin/env python3
"""Heuristic Agda implementation-substance classifier.

This tool does not decide mathematical truth.  It reports observable source
features that distinguish proof-bearing code from postulated interfaces,
constructor/refl ledgers, governance strings, and executable definitions.
The output is deterministic JSON suitable for CI and later longitudinal audits.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

POSTULATE_RE = re.compile(r"(?m)^\s*postulate\b")
HOLE_RE = re.compile(r"\{!.*?!\}|(?m)^\s*\?\s*(?:$|[;,)])", re.DOTALL)
UNSAFE_RE = re.compile(
    r"--allow-unsolved-metas|--no-termination-check|--no-positivity-check|"
    r"--type-in-type|--omega-in-omega|--unsafe|TERMINATING|NON_COVERING|"
    r"NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|trustMe|primTrustMe"
)
STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
BOOL_FIELD_RE = re.compile(r"(?m)^\s*[A-Za-z0-9_'-]+\s*:\s*Bool\s*$")
REFL_BODY_RE = re.compile(r"(?m)^\s*[A-Za-z0-9_'-]+(?:\s+[^=\n]+)?\s*=\s*refl\s*$")
DATA_RE = re.compile(r"(?m)^\s*data\s+[A-Za-z0-9_'.-]+")
RECORD_RE = re.compile(r"(?m)^\s*record\s+[A-Za-z0-9_'.-]+")
IMPORT_RE = re.compile(r"(?m)^\s*(?:open\s+)?import\s+")
EQUATION_RE = re.compile(r"(?m)^\s*[A-Za-z0-9_'-]+(?:\s+[^:=\n]+)+\s*=\s*(?!refl\b).+$")
THEOREM_SIGNATURE_RE = re.compile(
    r"(?m)^[A-Za-z][A-Za-z0-9_'-]*(?:\s*\{[^\n]*\})?\s*:"
)


@dataclass(frozen=True)
class FileMetrics:
    path: str
    lines: int
    imports: int
    data_declarations: int
    record_declarations: int
    theorem_signatures: int
    executable_equations: int
    refl_bodies: int
    bool_fields: int
    string_literals: int
    postulates: int
    holes: int
    unsafe_escapes: int
    category: str


def classify_text(path: str, text: str) -> FileMetrics:
    lines = text.count("\n") + (0 if text.endswith("\n") else 1)
    postulates = len(POSTULATE_RE.findall(text))
    holes = len(HOLE_RE.findall(text))
    unsafe = len(UNSAFE_RE.findall(text))
    imports = len(IMPORT_RE.findall(text))
    data_count = len(DATA_RE.findall(text))
    record_count = len(RECORD_RE.findall(text))
    theorem_count = len(THEOREM_SIGNATURE_RE.findall(text))
    equations = len(EQUATION_RE.findall(text))
    refl_count = len(REFL_BODY_RE.findall(text))
    bool_count = len(BOOL_FIELD_RE.findall(text))
    strings = len(STRING_RE.findall(text))

    if postulates or holes or unsafe:
        category = "external-or-unsafe-interface"
    elif equations >= 8 and theorem_count >= 4:
        category = "proof-bearing-computational"
    elif data_count + record_count >= 3 and equations >= 3:
        category = "structural-with-witnesses"
    elif strings + bool_count > equations + theorem_count and refl_count >= 3:
        category = "governance-or-constructor-ledger"
    elif refl_count > equations and theorem_count:
        category = "definitional-refl-surface"
    else:
        category = "mixed-or-thin-surface"

    return FileMetrics(
        path=path,
        lines=lines,
        imports=imports,
        data_declarations=data_count,
        record_declarations=record_count,
        theorem_signatures=theorem_count,
        executable_equations=equations,
        refl_bodies=refl_count,
        bool_fields=bool_count,
        string_literals=strings,
        postulates=postulates,
        holes=holes,
        unsafe_escapes=unsafe,
        category=category,
    )


def iter_agda_files(paths: Iterable[str]) -> Iterable[Path]:
    seen: set[Path] = set()
    for raw in paths:
        path = Path(raw)
        candidates = path.rglob("*.agda") if path.is_dir() else [path]
        for candidate in candidates:
            if candidate.suffix != ".agda":
                continue
            resolved = candidate.resolve()
            if resolved not in seen:
                seen.add(resolved)
                yield candidate


def self_test() -> None:
    proof = """module Proof where

data Bit : Set where zero one : Bit
flip : Bit -> Bit
flip zero = one
flip one = zero
involutive : (x : Bit) -> flip (flip x) == x
involutive zero = refl
involutive one = refl
"""
    ledger = """module Ledger where

open import Agda.Builtin.Bool
open import Agda.Builtin.String
record R : Set where
 field flag : Bool
       note : String
x : Bool
x = true
xIsTrue : x == true
xIsTrue = refl
"""
    unsafe = """module Unsafe where
postulate A : Set
"""

    proof_metrics = classify_text("proof.agda", proof)
    ledger_metrics = classify_text("ledger.agda", ledger)
    unsafe_metrics = classify_text("unsafe.agda", unsafe)

    assert proof_metrics.executable_equations >= 2
    assert proof_metrics.theorem_signatures >= 2
    assert proof_metrics.postulates == 0
    assert proof_metrics.holes == 0
    assert ledger_metrics.bool_fields >= 1
    assert unsafe_metrics.category == "external-or-unsafe-interface"
    assert unsafe_metrics.postulates == 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="*", default=["DASHI"])
    parser.add_argument("--output", type=Path)
    parser.add_argument("--fail-on-external", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        self_test()
        print("Agda substance classifier self-test passed")
        return 0

    metrics: list[FileMetrics] = []
    for path in iter_agda_files(args.paths):
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            print(f"failed to read {path}: {exc}", file=sys.stderr)
            return 2
        metrics.append(classify_text(str(path), text))

    metrics.sort(key=lambda item: item.path)
    summary: dict[str, int] = {}
    for item in metrics:
        summary[item.category] = summary.get(item.category, 0) + 1

    payload = {
        "schema": "dashi-agda-substance-v1",
        "files": [asdict(item) for item in metrics],
        "summary": summary,
    }
    rendered = json.dumps(payload, indent=2, sort_keys=True)

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered + "\n", encoding="utf-8")
    else:
        print(rendered)

    if args.fail_on_external and any(
        item.category == "external-or-unsafe-interface" for item in metrics
    ):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
