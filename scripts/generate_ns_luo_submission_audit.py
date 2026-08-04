#!/usr/bin/env python3
"""Generate a machine-readable audit for the Navier--Stokes Luo lane.

The report is intentionally syntactic.  It inventories modules, imports,
top-level declarations, source metadata, file hashes, explicit proof-level
markers, and the finite/infinite and rational/real boundary vocabulary.  It
also fails closed on holes, question-mark metavariable markers, postulates, or
unsafe/unsolved-meta options when --strict is supplied.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Iterable

MODULE_RE = re.compile(r"^module\s+([^\s]+)\s+where\s*$")
IMPORT_RE = re.compile(r"^(?:open\s+)?import\s+([^\s]+)")
DECL_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_\-′₀-₉]*)\s*:")
PROVENANCE_RE = re.compile(
    r"^--\s*(Author|Authors|Title|DOI|arXiv DOI|Venue/year|Springer|Relationship):\s*(.*)$"
)

FORBIDDEN_PATTERNS = {
    "hole": re.compile(r"\{!!\}"),
    "postulate": re.compile(r"^\s*postulate(?:\s|$)", re.MULTILINE),
    "unsolved_metas": re.compile(r"--allow-unsolved-metas"),
    "unsafe": re.compile(r"\{\-#\s*OPTIONS[^#]*--unsafe"),
    "question_marker": re.compile(r"\?(?:$|[^A-Za-z0-9_])", re.MULTILINE),
}

BOUNDARY_TERMS = {
    "finite": re.compile(r"\b[Ff]inite\b"),
    "infinite": re.compile(r"\b[Ii]nfinite\b"),
    "rational": re.compile(r"(?:\b[Rr]ational\b|ℚ)"),
    "real": re.compile(r"(?:\b[Rr]eal\b|ℝ)"),
    "standard_imported": re.compile(r"standardImported"),
    "machine_checked": re.compile(r"machineChecked"),
    "set_omega": re.compile(r"Setω"),
}


@dataclass(frozen=True)
class Finding:
    kind: str
    file: str
    line: int
    text: str


@dataclass(frozen=True)
class FileAudit:
    path: str
    sha256: str
    module: str | None
    imports: list[str]
    declarations: list[str]
    provenance: list[dict[str, str]]
    boundary_counts: dict[str, int]
    findings: list[Finding]


def repository_root() -> Path:
    return Path(__file__).resolve().parents[1]


def git_revision(root: Path) -> str | None:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def selected_files(root: Path) -> list[Path]:
    closure = root / "DASHI" / "Physics" / "Closure"
    files = sorted(closure.glob("NSTriadKNLuo*.agda"))
    final_statement = closure / "NSTriadKNPeriodicNavierStokesSubmissionTheoremExact.agda"
    if final_statement.exists():
        files.append(final_statement)
    return sorted(set(files))


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def findings_for(path: Path, text: str, root: Path) -> list[Finding]:
    rel = str(path.relative_to(root))
    findings: list[Finding] = []
    for kind, pattern in FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(text):
            findings.append(
                Finding(
                    kind=kind,
                    file=rel,
                    line=line_number(text, match.start()),
                    text=match.group(0),
                )
            )
    return findings


def provenance_for(lines: Iterable[str]) -> list[dict[str, str]]:
    result: list[dict[str, str]] = []
    for line in lines:
        match = PROVENANCE_RE.match(line)
        if match:
            result.append({"field": match.group(1), "value": match.group(2).strip()})
    return result


def audit_file(path: Path, root: Path) -> FileAudit:
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    lines = text.splitlines()

    module = None
    imports: list[str] = []
    declarations: list[str] = []

    for line in lines:
        if module is None:
            module_match = MODULE_RE.match(line)
            if module_match:
                module = module_match.group(1)
        import_match = IMPORT_RE.match(line)
        if import_match:
            imports.append(import_match.group(1))
        declaration_match = DECL_RE.match(line)
        if declaration_match:
            declarations.append(declaration_match.group(1))

    boundary_counts = {
        name: len(pattern.findall(text)) for name, pattern in BOUNDARY_TERMS.items()
    }

    return FileAudit(
        path=str(path.relative_to(root)),
        sha256=hashlib.sha256(raw).hexdigest(),
        module=module,
        imports=sorted(set(imports)),
        declarations=declarations,
        provenance=provenance_for(lines),
        boundary_counts=boundary_counts,
        findings=findings_for(path, text, root),
    )


def dependency_edges(files: list[FileAudit]) -> list[dict[str, str]]:
    modules = {item.module for item in files if item.module is not None}
    edges: list[dict[str, str]] = []
    for item in files:
        if item.module is None:
            continue
        for imported in item.imports:
            if imported in modules:
                edges.append({"from": item.module, "to": imported})
    return sorted(edges, key=lambda edge: (edge["from"], edge["to"]))


def report(root: Path) -> dict[str, object]:
    files = [audit_file(path, root) for path in selected_files(root)]
    findings = [asdict(finding) for item in files for finding in item.findings]

    provenance_entries = [
        {"file": item.path, **entry}
        for item in files
        for entry in item.provenance
    ]

    boundary_summary = {
        name: sum(item.boundary_counts[name] for item in files)
        for name in BOUNDARY_TERMS
    }

    return {
        "schema_version": 1,
        "repository_revision": git_revision(root),
        "file_count": len(files),
        "module_count": sum(item.module is not None for item in files),
        "declaration_count": sum(len(item.declarations) for item in files),
        "dependency_edges": dependency_edges(files),
        "provenance_inventory": provenance_entries,
        "boundary_summary": boundary_summary,
        "findings": findings,
        "files": [
            {
                **asdict(item),
                "findings": [asdict(finding) for finding in item.findings],
            }
            for item in files
        ],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        required=True,
        help="Path to the JSON report to create.",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Exit nonzero if forbidden findings are present.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = repository_root()
    payload = report(root)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    findings = payload["findings"]
    if args.strict and findings:
        print(
            f"submission audit failed with {len(findings)} forbidden finding(s)",
            file=sys.stderr,
        )
        for finding in findings:
            print(
                f"{finding['file']}:{finding['line']}: {finding['kind']}: "
                f"{finding['text']!r}",
                file=sys.stderr,
            )
        return 1

    print(
        "generated Luo submission audit: "
        f"{payload['file_count']} files, "
        f"{payload['declaration_count']} declarations, "
        f"{len(payload['dependency_edges'])} internal dependency edges"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
