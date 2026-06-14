#!/usr/bin/env python3
"""Audit Perelman / Bruhat-Tits geometry boundary Agda surfaces."""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


AUDIT_ID = "perelman_bt_geometry_boundary_audit"

REQUIRED_MODULES = (
    "DASHI.Physics.Closure.BTBallVolumeEntropyBoundary",
    "DASHI.Physics.Closure.BTGaussianReducedVolumeBoundary",
    "DASHI.Physics.Closure.BTNeckJSJGeometryAnalogueBoundary",
    "DASHI.Physics.Closure.PerelmanRicciFlowAndGeometrizationBoundaryReceipt",
    "DASHI.Physics.Closure.BTFiniteMetricGaugeCompatibilityKappaBoundary",
    "DASHI.Physics.Closure.BruhatTitsProductTreeReceipt",
)

REQUIRED_CATEGORIES: dict[str, tuple[str, ...]] = {
    "ball_formula_product_entropy_boundary": (
        "BTBallVolumeEntropyBoundary",
        "BruhatTitsProductTreeReceipt",
        "regularTreeBallFormulaText",
        "productBallFormulaText",
        "productAsymptoticFormulaText",
        "entropyLabelText",
        "canonicalEntropyLog42Recorded",
    ),
    "gaussian_convergence_non_monotonicity_socket": (
        "BTGaussianReducedVolumeBoundary",
        "gaussianReducedVolumeSeries",
        "convergenceFlagIsTrue",
        "monotonicityTheoremFlagIsFalse",
        "SmoothPerelmanMonotonicityTheoremPromoted",
        "canonicalMonotonicityFlagFalse",
        "≡ false",
    ),
    "bt_neck_jsj_geometry_analogue_boundary": (
        "BTNeckJSJGeometryAnalogueBoundary",
        "BTNeckAnalogue",
        "JSJAnalogue",
        "GeometryAnalogue",
        "geometrizationProvedHereIsFalse",
        "boundaryGeometrizationBlocked",
        "≡ false",
    ),
    "perelman_authority_sockets_false": (
        "PerelmanRicciFlowAndGeometrizationBoundaryReceipt",
        "AuthoritySocket",
        "authorityAvailableIsFalse",
        "smoothRicciFlowExistenceUniquenessSocket",
        "reducedVolumeMonotonicitySocket",
        "thurstonGeometrizationSocket",
        "allPerelmanBoundaryAuthoritySocketsClosed",
        "thurstonGeometrizationAuthorityNotPromoted",
        "≡ false",
    ),
    "finite_kappa_and_product_tree_import_boundary": (
        "BTFiniteMetricGaugeCompatibilityKappaBoundary",
        "canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary",
        "BruhatTitsProductTreeReceipt",
        "canonicalBruhatTitsProductTreeReceipt",
        "clayYangMillsPromotedIsFalse",
        "terminalClayClaimPromotedIsFalse",
    ),
}

MODULE_CATEGORY_HINTS: dict[str, tuple[str, ...]] = {
    "DASHI.Physics.Closure.BTBallVolumeEntropyBoundary": (
        "ball_formula_product_entropy_boundary",
        "finite_kappa_and_product_tree_import_boundary",
    ),
    "DASHI.Physics.Closure.BTGaussianReducedVolumeBoundary": (
        "gaussian_convergence_non_monotonicity_socket",
    ),
    "DASHI.Physics.Closure.BTNeckJSJGeometryAnalogueBoundary": (
        "bt_neck_jsj_geometry_analogue_boundary",
    ),
    "DASHI.Physics.Closure.PerelmanRicciFlowAndGeometrizationBoundaryReceipt": (
        "perelman_authority_sockets_false",
    ),
    "DASHI.Physics.Closure.BTFiniteMetricGaugeCompatibilityKappaBoundary": (
        "finite_kappa_and_product_tree_import_boundary",
    ),
    "DASHI.Physics.Closure.BruhatTitsProductTreeReceipt": (
        "ball_formula_product_entropy_boundary",
        "finite_kappa_and_product_tree_import_boundary",
    ),
}

INCOMPLETE_MARKERS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("postulate", re.compile(r"(?<![A-Za-z0-9_])post" + r"ulate(?![A-Za-z0-9_])")),
    ("agda-hole", re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}"))),
    ("rhs-meta", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9'_]*\s*(?::[^=\n]+)?=\s*\?\s*$")),
)


@dataclass(frozen=True)
class ModuleSurface:
    module: str
    path: Path
    exists: bool
    text: str
    read_error: str | None = None

    @property
    def relpath(self) -> str:
        return module_to_path(self.module).as_posix()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--markdown-out", type=Path, default=None)
    parser.add_argument("--allow-missing-aggregate", action="store_true")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def module_to_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".agda")


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def read_surface(repo_root: Path, module: str) -> ModuleSurface:
    rel = module_to_path(module)
    path = repo_root / rel
    if not path.exists():
        return ModuleSurface(module=module, path=path, exists=False, text="")
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
        return ModuleSurface(module=module, path=path, exists=True, text=text)
    except OSError as exc:
        return ModuleSurface(module=module, path=path, exists=True, text="", read_error=str(exc))


def marker_hits(surface: ModuleSurface) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for marker, pattern in INCOMPLETE_MARKERS:
        for match in pattern.finditer(surface.text):
            hits.append(
                {
                    "module": surface.module,
                    "path": surface.relpath,
                    "line": line_for_offset(surface.text, match.start()),
                    "marker": marker,
                }
            )
    return hits


def category_status(surfaces: list[ModuleSurface]) -> dict[str, dict[str, Any]]:
    combined = "\n".join(surface.text for surface in surfaces if surface.exists)
    status: dict[str, dict[str, Any]] = {}
    for category, tokens in REQUIRED_CATEGORIES.items():
        missing = [token for token in tokens if token not in combined]
        present_modules = [
            surface.module
            for surface in surfaces
            if surface.exists and any(token in surface.text for token in tokens)
        ]
        status[category] = {
            "passed": not missing,
            "missing_tokens": missing,
            "present_modules": present_modules,
            "required_tokens": list(tokens),
        }
    return status


def module_status(surface: ModuleSurface) -> dict[str, Any]:
    module_decl = f"module {surface.module} where"
    categories = MODULE_CATEGORY_HINTS.get(surface.module, ())
    category_hits = {
        category: [
            token for token in REQUIRED_CATEGORIES[category] if surface.exists and token in surface.text
        ]
        for category in categories
    }
    hits = marker_hits(surface) if surface.exists else []
    return {
        "module": surface.module,
        "path": surface.relpath,
        "exists": surface.exists,
        "readable": surface.exists and surface.read_error is None,
        "read_error": surface.read_error,
        "module_declaration_present": surface.exists and module_decl in surface.text,
        "incomplete_marker_hits": hits,
        "no_incomplete_markers": not hits,
        "category_hits": category_hits,
    }


def aggregate_status(repo_root: Path, modules: tuple[str, ...]) -> dict[str, Any]:
    path = repo_root / "DASHI" / "Everything.agda"
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except FileNotFoundError:
        return {
            "path": "DASHI/Everything.agda",
            "exists": False,
            "included_modules": [],
            "missing_modules": list(modules),
            "passed": False,
        }
    included = [module for module in modules if f"import {module}" in text]
    missing = [module for module in modules if module not in included]
    return {
        "path": "DASHI/Everything.agda",
        "exists": True,
        "included_modules": included,
        "missing_modules": missing,
        "passed": not missing,
    }


def check_rows(
    modules: list[dict[str, Any]],
    categories: dict[str, dict[str, Any]],
    aggregate: dict[str, Any],
    allow_missing_aggregate: bool,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in modules:
        rows.append(
            {
                "name": f"module:{item['module']}",
                "kind": "module",
                "passed": bool(
                    item["exists"]
                    and item["readable"]
                    and item["module_declaration_present"]
                    and item["no_incomplete_markers"]
                ),
                "path": item["path"],
            }
        )
    for name, item in categories.items():
        rows.append(
            {
                "name": f"category:{name}",
                "kind": "category",
                "passed": item["passed"],
                "missing_tokens": item["missing_tokens"],
                "present_modules": item["present_modules"],
            }
        )
    rows.append(
        {
            "name": "aggregate:DASHI.Everything",
            "kind": "aggregate",
            "passed": bool(aggregate["passed"] or allow_missing_aggregate),
            "missing_modules": aggregate["missing_modules"],
        }
    )
    return rows


def build_summary(repo_root: Path, allow_missing_aggregate: bool) -> dict[str, Any]:
    surfaces = [read_surface(repo_root, module) for module in REQUIRED_MODULES]
    modules = [module_status(surface) for surface in surfaces]
    categories = category_status(surfaces)
    aggregate = aggregate_status(repo_root, REQUIRED_MODULES)
    checks = check_rows(modules, categories, aggregate, allow_missing_aggregate)

    failed_required: list[str] = []
    for item in modules:
        if not item["exists"]:
            failed_required.append(f"missing module {item['module']}")
        if not item["readable"]:
            failed_required.append(f"unreadable module {item['module']}")
        if not item["module_declaration_present"]:
            failed_required.append(f"missing module declaration {item['module']}")
        if not item["no_incomplete_markers"]:
            failed_required.append(f"incomplete markers in {item['module']}")
    for name, item in categories.items():
        if not item["passed"]:
            failed_required.append(f"missing boundary tokens for {name}")
    if not aggregate["passed"] and not allow_missing_aggregate:
        failed_required.append("missing aggregate imports")

    return {
        "audit_id": AUDIT_ID,
        "repo_root": str(repo_root),
        "required_modules": list(REQUIRED_MODULES),
        "module_count": len(REQUIRED_MODULES),
        "modules": modules,
        "category_checks": categories,
        "aggregate_import_status": aggregate,
        "checks": checks,
        "allow_missing_aggregate": allow_missing_aggregate,
        "failed_required_checks": failed_required,
        "passed": not failed_required,
        "control_card": {
            "O": "Audit owns only textual boundary checks over Perelman/Ricci-flow and Bruhat-Tits geometry Agda surfaces.",
            "R": "Require BT ball-volume/product-entropy, Gaussian reduced-volume, neck/JSJ analogue, Perelman authority, finite-kappa, and product-tree receipt surfaces.",
            "C": "Stdlib Python argparse script emits JSON and optional Markdown from repo-local Agda text.",
            "S": "The current repo may have downstream BT receipts while the Perelman geometry boundary modules are not yet present.",
            "L": "Required modules -> no postulates/holes/rhs metas -> boundary tokens -> aggregate import visibility.",
            "P": "Fail closed on missing modules, marker hits, missing boundary tokens, and aggregate omissions unless aggregate relaxation is explicit.",
            "G": "Audit does not typecheck Agda, prove Perelman/Ricci-flow claims, or grant external mathematical authority.",
            "F": "This is textual hygiene for boundary sockets, not a semantic proof checker.",
        },
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# Perelman BT Geometry Boundary Audit",
        "",
        f"- Audit: `{summary['audit_id']}`",
        f"- Passed: `{summary['passed']}`",
        f"- Allow missing aggregate: `{summary['allow_missing_aggregate']}`",
        "",
        "## Modules",
        "",
        "| Module | Exists | Decl | No markers |",
        "| --- | ---: | ---: | ---: |",
    ]
    for item in summary["modules"]:
        lines.append(
            f"| `{item['module']}` | `{item['exists']}` | "
            f"`{item['module_declaration_present']}` | `{item['no_incomplete_markers']}` |"
        )
    lines.extend(["", "## Category Checks", ""])
    for name, item in summary["category_checks"].items():
        missing = ", ".join(f"`{token}`" for token in item["missing_tokens"]) or "none"
        lines.append(f"- `{name}`: passed=`{item['passed']}`, missing={missing}")
    aggregate = summary["aggregate_import_status"]
    missing_aggregate = ", ".join(f"`{module}`" for module in aggregate["missing_modules"]) or "none"
    lines.extend(
        [
            "",
            "## Aggregate",
            "",
            f"- Path: `{aggregate['path']}`",
            f"- Passed: `{aggregate['passed']}`",
            f"- Missing imports: {missing_aggregate}",
            "",
            "## Failed Required Checks",
            "",
        ]
    )
    if summary["failed_required_checks"]:
        lines.extend(f"- {item}" for item in summary["failed_required_checks"])
    else:
        lines.append("- none")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    summary = build_summary(repo_root, args.allow_missing_aggregate)
    if args.markdown_out is not None:
        md_path = args.markdown_out
        if not md_path.is_absolute():
            md_path = repo_root / md_path
        md_path.parent.mkdir(parents=True, exist_ok=True)
        md_path.write_text(render_markdown(summary), encoding="utf-8")
        summary["markdown_out"] = str(md_path)
    indent = 2 if args.pretty else None
    print(json.dumps(summary, indent=indent, sort_keys=True))
    return 0 if summary["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
