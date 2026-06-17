#!/usr/bin/env python3
"""Audit the PNF numeric ABI surface across Python and Agda text.

This is a static inspection helper only. It does not invoke Agda or import the
sibling repository. The script compares the Python ABI surface described by
``itir_mcp.pnf_numeric_abi`` against the requested Agda module path if present
and reports covered versus missing names.
"""

from __future__ import annotations

import argparse
import ast
import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PYTHON_PATH = (
    REPO_ROOT.parent / "ITIR-suite" / "itir-mcp" / "src" / "itir_mcp" / "pnf_numeric_abi.py"
)
DEFAULT_AGDA_PATH = REPO_ROOT / "DASHI" / "Interop" / "PNFSpectralNumericABICore.agda"


PAYLOAD_GET_RE = re.compile(r'payload\.get\("([^"]+)"\)')
TOP_LEVEL_SIG_RE = re.compile(r"(?m)^([A-Za-z][A-Za-z0-9']*)\s*:")
TOP_LEVEL_DECL_RE = re.compile(r"(?m)^(?:data|record|postulate)\s+([A-Za-z][A-Za-z0-9']*)\b")
MODULE_RE = re.compile(r"(?m)^module\s+([A-Za-z][A-Za-z0-9'.]*)\s+where\b")


@dataclass
class Surface:
    present: bool
    path: str
    names: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)
    module_name: str | None = None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--python-path", type=Path, default=DEFAULT_PYTHON_PATH)
    parser.add_argument("--agda-path", type=Path, default=DEFAULT_AGDA_PATH)
    parser.add_argument("--limit", type=int, default=24, help="Max names shown per list.")
    parser.add_argument("--json-only", action="store_true", help="Print only the JSON payload.")
    return parser.parse_args()


def rel(path: Path) -> str:
    try:
        return path.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return str(path)


def read_text(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return None


def unique(items: list[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def collect_python_surface(path: Path) -> Surface:
    text = read_text(path)
    if text is None:
        return Surface(
            present=False,
            path=rel(path),
            notes=["python source not readable"],
        )

    tree = ast.parse(text, filename=str(path))
    names: list[str] = []
    notes: list[str] = []

    for node in tree.body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    names.append(target.id)
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            names.append(node.target.id)
        elif isinstance(node, ast.FunctionDef):
            names.append(node.name)

    class RuntimeFieldVisitor(ast.NodeVisitor):
        def __init__(self) -> None:
            self.fields: list[str] = []

        def visit_Call(self, node: ast.Call) -> Any:
            if isinstance(node.func, ast.Attribute) and node.func.attr == "get":
                value = node.func.value
                if isinstance(value, ast.Name) and value.id == "payload":
                    if node.args and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, str):
                        self.fields.append(node.args[0].value)
            self.generic_visit(node)

        def visit_Dict(self, node: ast.Dict) -> Any:
            for key in node.keys:
                if isinstance(key, ast.Constant) and isinstance(key.value, str):
                    self.fields.append(key.value)
            self.generic_visit(node)

    visitor = RuntimeFieldVisitor()
    visitor.visit(tree)

    names.extend(visitor.fields)
    names = unique(names)
    notes.append("static AST scan of module-level names and payload dict fields")

    return Surface(present=True, path=rel(path), names=sorted(names), notes=notes)


def collect_agda_surface(path: Path) -> Surface:
    text = read_text(path)
    if text is None:
        return Surface(
            present=False,
            path=rel(path),
            notes=["Agda module file missing or unreadable"],
        )

    names: list[str] = []
    module_match = MODULE_RE.search(text)
    module_name = module_match.group(1) if module_match else None
    names.extend(TOP_LEVEL_SIG_RE.findall(text))
    names.extend(TOP_LEVEL_DECL_RE.findall(text))
    names = unique(names)

    return Surface(
        present=True,
        path=rel(path),
        names=sorted(names),
        notes=["static text scan of top-level signatures and declarations"],
        module_name=module_name,
    )


def build_report(py_surface: Surface, agda_surface: Surface, limit: int) -> dict[str, Any]:
    shared = sorted(set(py_surface.names) & set(agda_surface.names))
    missing_from_agda = sorted(set(py_surface.names) - set(agda_surface.names))
    covered = shared

    return {
        "status": "ok" if agda_surface.present else "agda_missing",
        "python": {
            "present": py_surface.present,
            "path": py_surface.path,
            "names": py_surface.names[:limit],
            "count": len(py_surface.names),
            "notes": py_surface.notes,
        },
        "agda": {
            "present": agda_surface.present,
            "path": agda_surface.path,
            "names": agda_surface.names[:limit],
            "count": len(agda_surface.names),
            "notes": agda_surface.notes,
        },
        "coverage": {
            "shared": shared[:limit],
            "shared_count": len(shared),
            "covered": covered[:limit],
            "covered_count": len(covered),
            "missing_from_agda": missing_from_agda[:limit],
            "missing_from_agda_count": len(missing_from_agda),
        },
    }


def render_markdownish(report: dict[str, Any]) -> str:
    python_block = report["python"]
    agda_block = report["agda"]
    coverage = report["coverage"]

    lines = [
        "PNF numeric ABI surface audit",
        f"- python: {'present' if python_block['present'] else 'missing'} ({python_block['path']})",
        f"- agda: {'present' if agda_block['present'] else 'missing'} ({agda_block['path']})",
        f"- shared exact names: {coverage['shared_count']}",
        f"- missing from agda: {coverage['missing_from_agda_count']}",
        "",
        "Covered:",
        "  " + (", ".join(coverage["covered"]) if coverage["covered"] else "none"),
        "Missing:",
        "  " + (", ".join(coverage["missing_from_agda"]) if coverage["missing_from_agda"] else "none"),
    ]
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    py_surface = collect_python_surface(args.python_path)
    agda_surface = collect_agda_surface(args.agda_path)
    report = build_report(py_surface, agda_surface, args.limit)

    if args.json_only:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, indent=2, sort_keys=True))
        print()
        print(render_markdownish(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
