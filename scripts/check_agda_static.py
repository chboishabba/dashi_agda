#!/usr/bin/env python3
"""Lightweight Agda structural audit.

This is deliberately NOT an Agda typechecker. It provides cheap V1 checks:
- module declaration matches repository path;
- DASHI imports resolve to source files;
- strings/comments/delimiters are structurally balanced;
- optional required symbols are present;
- if tree-sitter-agda is installed, parser ERROR/MISSING nodes are reported.

The authoritative semantic receipt remains Agda itself.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Iterable

MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z0-9_.']+)\s+where\s*$", re.MULTILINE)
IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.']+)", re.MULTILINE)
TOP_SYMBOL_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_'-]*)\s*(?::|=)", re.MULTILINE)


@dataclass
class Finding:
    severity: str
    path: str
    code: str
    message: str


def expected_module_for(path: Path, repo_root: Path) -> str | None:
    try:
        rel = path.resolve().relative_to(repo_root.resolve())
    except ValueError:
        return None
    if rel.suffix != ".agda":
        return None
    return ".".join(rel.with_suffix("").parts)


def scan_lexical_structure(text: str) -> list[str]:
    """Check nested block comments, quoted strings, and (), [], {} balance.

    Agda block comments nest. Line comments run from -- to newline. Characters
    inside comments/strings are ignored for delimiter balancing.
    """
    errors: list[str] = []
    stack: list[tuple[str, int]] = []
    block_depth = 0
    in_string = False
    escaped = False
    i = 0
    pairs = {")": "(", "]": "[", "}": "{"}

    while i < len(text):
        c = text[i]
        n = text[i + 1] if i + 1 < len(text) else ""

        if block_depth:
            if c == "{" and n == "-":
                block_depth += 1
                i += 2
                continue
            if c == "-" and n == "}":
                block_depth -= 1
                i += 2
                continue
            i += 1
            continue

        if in_string:
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                in_string = False
            i += 1
            continue

        if c == "-" and n == "-":
            j = text.find("\n", i + 2)
            i = len(text) if j < 0 else j + 1
            continue
        if c == "{" and n == "-":
            block_depth = 1
            i += 2
            continue
        if c == '"':
            in_string = True
            i += 1
            continue
        if c in "([{":
            stack.append((c, i))
        elif c in ")]}" :
            if not stack or stack[-1][0] != pairs[c]:
                errors.append(f"unmatched closing delimiter {c!r} at byte {i}")
            else:
                stack.pop()
        i += 1

    if block_depth:
        errors.append(f"unterminated nested block comment (depth {block_depth})")
    if in_string:
        errors.append("unterminated string literal")
    for opener, pos in reversed(stack):
        errors.append(f"unclosed delimiter {opener!r} at byte {pos}")
    return errors


def tree_sitter_errors(text: str) -> list[str]:
    """Use tree-sitter-agda when available; silently skip when absent."""
    try:
        from tree_sitter import Language, Parser  # type: ignore
        import tree_sitter_agda  # type: ignore
    except Exception:
        return []

    try:
        language = Language(tree_sitter_agda.language())
        parser = Parser(language)
        tree = parser.parse(text.encode("utf-8"))
    except Exception as exc:  # package/API mismatch should be visible but nonfatal
        return [f"tree-sitter unavailable at runtime: {exc}"]

    out: list[str] = []
    todo = [tree.root_node]
    while todo:
        node = todo.pop()
        if node.type == "ERROR" or node.is_missing:
            out.append(
                f"tree-sitter {node.type} at {node.start_point[0] + 1}:"
                f"{node.start_point[1] + 1}-{node.end_point[0] + 1}:"
                f"{node.end_point[1] + 1}"
            )
        todo.extend(node.children)
    return out


def audit_file(path: Path, repo_root: Path, required: Iterable[str]) -> list[Finding]:
    findings: list[Finding] = []
    try:
        text = path.read_text(encoding="utf-8")
    except Exception as exc:
        return [Finding("error", str(path), "read", str(exc))]

    module_match = MODULE_RE.search(text)
    expected = expected_module_for(path, repo_root)
    if not module_match:
        findings.append(Finding("error", str(path), "module-missing", "module declaration not found"))
    elif expected and module_match.group(1) != expected:
        findings.append(
            Finding(
                "error", str(path), "module-path-mismatch",
                f"declares {module_match.group(1)!r}; path implies {expected!r}",
            )
        )

    for err in scan_lexical_structure(text):
        findings.append(Finding("error", str(path), "lexical-structure", err))

    for err in tree_sitter_errors(text):
        severity = "warning" if err.startswith("tree-sitter unavailable") else "error"
        findings.append(Finding(severity, str(path), "tree-sitter", err))

    for mod in IMPORT_RE.findall(text):
        if not mod.startswith("DASHI."):
            continue
        target = repo_root.joinpath(*mod.split(".")).with_suffix(".agda")
        if not target.exists():
            findings.append(
                Finding("error", str(path), "missing-import", f"{mod} -> {target.relative_to(repo_root)}")
            )

    symbols = set(TOP_SYMBOL_RE.findall(text))
    for symbol in required:
        if symbol not in symbols and re.search(rf"\b{re.escape(symbol)}\b", text) is None:
            findings.append(Finding("error", str(path), "missing-symbol", symbol))

    return findings


def self_test() -> int:
    cases = [
        ("module DASHI.X where\nfoo : Set\nfoo = Set\n", []),
        ("module DASHI.X where\nfoo = (\n", ["unclosed delimiter"]),
        ("module DASHI.X where\n{- a {- b -} c -}\nfoo = Set\n", []),
        ('module DASHI.X where\nfoo = "("\n', []),
    ]
    failed = 0
    for i, (text, expected_errors) in enumerate(cases, 1):
        got = scan_lexical_structure(text)
        for needle in expected_errors:
            if not any(needle in item for item in got):
                print(f"self-test {i}: expected {needle!r}, got {got!r}", file=sys.stderr)
                failed += 1
        if not expected_errors and got:
            print(f"self-test {i}: unexpected {got!r}", file=sys.stderr)
            failed += 1
    if failed == 0:
        print("check_agda_static.py self-test: PASS")
    return 1 if failed else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="*", type=Path)
    ap.add_argument("--repo-root", type=Path, default=Path.cwd())
    ap.add_argument("--require", action="append", default=[], metavar="PATH:SYMBOL")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not args.paths:
        ap.error("provide one or more .agda paths, or --self-test")

    requirements: dict[str, list[str]] = {}
    for item in args.require:
        if ":" not in item:
            ap.error(f"--require expects PATH:SYMBOL, got {item!r}")
        file_name, symbol = item.rsplit(":", 1)
        requirements.setdefault(str(Path(file_name)), []).append(symbol)

    findings: list[Finding] = []
    for path in args.paths:
        findings.extend(audit_file(path, args.repo_root, requirements.get(str(path), [])))

    if args.json:
        print(json.dumps([asdict(x) for x in findings], indent=2, ensure_ascii=False))
    else:
        for f in findings:
            print(f"{f.severity.upper()} {f.path}: {f.code}: {f.message}")
        if not findings:
            print(f"static Agda audit: PASS ({len(args.paths)} files)")

    return 1 if any(f.severity == "error" for f in findings) else 0


if __name__ == "__main__":
    raise SystemExit(main())
