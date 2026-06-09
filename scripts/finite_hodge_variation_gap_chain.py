#!/usr/bin/env python3
"""Emit the finite Hodge variation gap chain artifacts."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
from typing import Any


ARTIFACT_ID = "finite_hodge_variation_gap_chain"
DEFAULT_OUT_DIR = Path("outputs") / ARTIFACT_ID

SUPPORT_MODULES: tuple[dict[str, str], ...] = (
    {
        "module": "BTFiniteHodgeStarObligation",
        "path": "DASHI/Physics/Closure/BTFiniteHodgeStarObligation.agda",
        "support": (
            "Records the finite BT Hodge target, 11 canonical rows, exact "
            "blockers, finite exterior derivative availability, and false "
            "promotion flags for metric Hodge star, pairing, IBP, d*F=J, "
            "dJ=0, Maxwell, YM, and terminal promotion."
        ),
    },
    {
        "module": "BTFiniteHodgeEffectiveActionTheoremBoundary",
        "path": "DASHI/Physics/Closure/BTFiniteHodgeEffectiveActionTheoremBoundary.agda",
        "support": (
            "Names the finite-depth BT complex, finite gauge field, finite "
            "Hodge star, finite effective action sum, Euler-Lagrange "
            "D_A^*F_A=J target, and current-conservation target while "
            "preserving exact matter/source and real sourced-equation blockers."
        ),
    },
    {
        "module": "HodgeVariationPairingDepth9",
        "path": "DASHI/Physics/Closure/HodgeVariationPairingDepth9.agda",
        "support": (
            "Packages the depth-9 connection, selected lower Hodge variation "
            "candidate, zero finite IBP law, selected lower D*F=J law, and "
            "the exact missingVariationPairingForSelectedHodgeStar blocker."
        ),
    },
    {
        "module": "YMStrictSelectedHodgeVariationPairing",
        "path": "DASHI/Physics/Closure/YMStrictSelectedHodgeVariationPairing.agda",
        "support": (
            "Calculates the strict selected finite Hodge variation pairing, "
            "selected D*F equals selected current, and discrete IBP split over "
            "user-supplied finite variation/action carriers without physical "
            "YM promotion."
        ),
    },
    {
        "module": "YMStrictHodgeVariationBlockerIndex",
        "path": "DASHI/Promotion/YMStrictHodgeVariationBlockerIndex.agda",
        "support": (
            "Indexes the strict selected finite pairing calculation, inhabited "
            "pure zero-current D*F=J, finite IBP lower law, exact strict "
            "variation blocker, exact physical source blocker, and false "
            "strict YM promotion."
        ),
    },
)

CHAIN_ROWS: tuple[dict[str, Any], ...] = (
    {
        "order": 1,
        "stage": "finite_cochain_complex",
        "statement": "Cochains C^k(K) with coboundary d_k and d_{k+1} d_k = 0.",
        "current_gap": "Finite-depth BT carrier and incidence/coboundary package is named as a target, not fully promoted as a metric complex.",
        "repo_support_modules": ["BTFiniteHodgeStarObligation"],
        "status": "supported_target_with_gap",
    },
    {
        "order": 2,
        "stage": "metric_hodge_star",
        "statement": "Metric Hodge star *: C^k(K) -> C^{n-k}(K^vee) from weighted primal/dual cells.",
        "current_gap": "Weighted primal/dual cells and metric Hodge star construction remain explicit blockers.",
        "repo_support_modules": ["BTFiniteHodgeStarObligation", "BTFiniteHodgeEffectiveActionTheoremBoundary"],
        "status": "blocked",
    },
    {
        "order": 3,
        "stage": "star_square_sign_law",
        "statement": "** obeys the finite degree/sign law, e.g. ** alpha = (-1)^{k(n-k)} alpha after the selected convention.",
        "current_gap": "The BT metric ** law is a named obligation and is not promoted.",
        "repo_support_modules": ["BTFiniteHodgeStarObligation"],
        "status": "blocked",
    },
    {
        "order": 4,
        "stage": "weighted_pairing",
        "statement": "Weighted pairing <alpha,beta> = sum_K alpha wedge * beta, compatible with the finite metric Hodge star.",
        "current_gap": "Finite selected lower pairing is calculated, but BT weighted pairing promotion is still false.",
        "repo_support_modules": [
            "BTFiniteHodgeStarObligation",
            "HodgeVariationPairingDepth9",
            "YMStrictSelectedHodgeVariationPairing",
            "YMStrictHodgeVariationBlockerIndex",
        ],
        "status": "partially_supported_with_gap",
    },
    {
        "order": 5,
        "stage": "finite_integration_by_parts",
        "statement": "Finite IBP: <d alpha,beta> = <alpha,d* beta> plus the selected boundary term.",
        "current_gap": "Strict selected finite IBP lower law is inhabited, while BT finite IBP promotion remains false.",
        "repo_support_modules": [
            "BTFiniteHodgeStarObligation",
            "HodgeVariationPairingDepth9",
            "YMStrictSelectedHodgeVariationPairing",
            "YMStrictHodgeVariationBlockerIndex",
        ],
        "status": "partially_supported_with_gap",
    },
    {
        "order": 6,
        "stage": "maxwell_equations",
        "statement": "Maxwell stack: dF = 0, d*F = J, and dJ = 0 from d^2 = 0 after the sourced equation is identified.",
        "current_gap": "Symbolic dF support exists; inhomogeneous d*F=J, source conservation dJ=0, calibration, and empirical authority remain blockers.",
        "repo_support_modules": ["BTFiniteHodgeStarObligation", "BTFiniteHodgeEffectiveActionTheoremBoundary"],
        "status": "partially_supported_with_gap",
    },
    {
        "order": 7,
        "stage": "yang_mills_curvature",
        "statement": "YM curvature F_A = dA + A wedge A on the finite gauge-field carrier.",
        "current_gap": "Finite gauge-field and effective-action targets are named; physical nonzero sourced YM promotion is not supplied.",
        "repo_support_modules": ["BTFiniteHodgeEffectiveActionTheoremBoundary", "YMStrictSelectedHodgeVariationPairing"],
        "status": "supported_target_with_gap",
    },
    {
        "order": 8,
        "stage": "yang_mills_euler_lagrange",
        "statement": "Finite YM Euler-Lagrange target d_A * F_A = J from the variation of the finite action.",
        "current_gap": "Selected finite variation/IBP calculation is present, but matter-current authority and real D_A^*F_A=J remain exact blockers.",
        "repo_support_modules": [
            "BTFiniteHodgeEffectiveActionTheoremBoundary",
            "YMStrictSelectedHodgeVariationPairing",
            "YMStrictHodgeVariationBlockerIndex",
        ],
        "status": "partially_supported_with_gap",
    },
    {
        "order": 9,
        "stage": "finite_hamiltonian",
        "statement": "Finite Hamiltonian derived from the gauge-invariant finite action and Hodge pairing.",
        "current_gap": "Finite effective action sum is named, but a self-adjoint real-carrier YM Hamiltonian is listed as not supplied.",
        "repo_support_modules": ["BTFiniteHodgeEffectiveActionTheoremBoundary", "YMStrictHodgeVariationBlockerIndex"],
        "status": "blocked",
    },
    {
        "order": 10,
        "stage": "gauge_invariant_spectral_gap",
        "statement": "Gauge-invariant non-vacuum spectral gap for the finite Hamiltonian.",
        "current_gap": "No promoted self-adjoint Hamiltonian or finite spectral-gap theorem is supplied by the named Hodge variation supports.",
        "repo_support_modules": ["YMStrictHodgeVariationBlockerIndex"],
        "status": "open_gap",
    },
    {
        "order": 11,
        "stage": "uniform_lower_bound",
        "statement": "Uniform positive lower bound on finite gauge-invariant spectral gaps across the selected approximation family.",
        "current_gap": "Uniform lower-bound transfer is outside the named Hodge supports and remains unpromoted for this chain.",
        "repo_support_modules": ["BTFiniteHodgeEffectiveActionTheoremBoundary"],
        "status": "open_gap",
    },
    {
        "order": 12,
        "stage": "continuum_transfer",
        "statement": "Continuum transfer of the finite lower bound to the continuum YM Hamiltonian and mass-gap statement.",
        "current_gap": "Continuum mass-gap, Clay YM, and terminal promotion remain false in the named boundary receipts.",
        "repo_support_modules": ["BTFiniteHodgeEffectiveActionTheoremBoundary", "YMStrictHodgeVariationBlockerIndex"],
        "status": "open_gap",
    },
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    parser.add_argument(
        "--generated-at",
        required=True,
        help="Deterministic generation timestamp or build label to embed in artifacts.",
    )
    return parser.parse_args()


def repo_relative(repo_root: Path, path: Path) -> str:
    return path.resolve().relative_to(repo_root.resolve()).as_posix()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_supports(repo_root: Path) -> list[dict[str, Any]]:
    supports: list[dict[str, Any]] = []
    failures: list[str] = []
    for support in SUPPORT_MODULES:
        rel_path = support["path"]
        path = repo_root / rel_path
        if not path.is_file():
            failures.append(f"missing support module: {rel_path}")
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        if support["module"] not in text:
            failures.append(f"support module token not found in {rel_path}: {support['module']}")
        supports.append(
            {
                "module": support["module"],
                "path": rel_path,
                "sha256": sha256_file(path),
                "support": support["support"],
            }
        )
    if failures:
        raise SystemExit("fail-closed support validation failed:\n" + "\n".join(failures))
    return supports


def normalize_rows(supports: list[dict[str, Any]]) -> list[dict[str, Any]]:
    support_by_module = {support["module"]: support for support in supports}
    rows: list[dict[str, Any]] = []
    for row in CHAIN_ROWS:
        modules = list(row["repo_support_modules"])
        rows.append(
            {
                "artifact_id": ARTIFACT_ID,
                "order": row["order"],
                "stage": row["stage"],
                "statement": row["statement"],
                "current_gap": row["current_gap"],
                "status": row["status"],
                "repo_supports": [
                    {
                        "module": module,
                        "path": support_by_module[module]["path"],
                    }
                    for module in modules
                ],
            }
        )
    return rows


def write_json(path: Path, payload: Any) -> None:
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "artifact_id",
        "order",
        "stage",
        "status",
        "statement",
        "current_gap",
        "repo_support_modules",
        "repo_support_paths",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    "artifact_id": row["artifact_id"],
                    "order": row["order"],
                    "stage": row["stage"],
                    "status": row["status"],
                    "statement": row["statement"],
                    "current_gap": row["current_gap"],
                    "repo_support_modules": ";".join(
                        support["module"] for support in row["repo_supports"]
                    ),
                    "repo_support_paths": ";".join(
                        support["path"] for support in row["repo_supports"]
                    ),
                }
            )


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        f"# {ARTIFACT_ID}",
        "",
        f"- generated_at: `{summary['generated_at']}`",
        f"- chain_rows: `{summary['chain_row_count']}`",
        f"- support_modules: `{summary['support_module_count']}`",
        f"- terminal_promotion: `{summary['terminal_promotion']}`",
        "",
        "## Gap chain",
        "",
        "| order | stage | status | current gap | repo supports |",
        "| ---: | --- | --- | --- | --- |",
    ]
    for row in rows:
        supports = ", ".join(support["module"] for support in row["repo_supports"])
        lines.append(
            "| {order} | {stage} | {status} | {gap} | {supports} |".format(
                order=row["order"],
                stage=row["stage"],
                status=row["status"],
                gap=row["current_gap"],
                supports=supports,
            )
        )
    lines.extend(
        [
            "",
            "## Continuum transfer status",
            "",
            "The finite Hodge/YM stack is organized as a promoted-target chain with "
            "explicit blockers. The named support modules do not promote Maxwell, "
            "physical Yang-Mills, Clay Yang-Mills, continuum mass gap, or terminal "
            "unification; the current output preserves those gaps.",
            "",
        ]
    )
    return "\n".join(lines)


def build_manifest(
    repo_root: Path,
    out_dir: Path,
    generated_at: str,
    artifact_paths: list[Path],
) -> dict[str, Any]:
    return {
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "output_dir": repo_relative(repo_root, out_dir),
        "artifacts": [
            {
                "path": repo_relative(repo_root, path),
                "size_bytes": path.stat().st_size,
                "sha256": sha256_file(path),
            }
            for path in artifact_paths
        ],
    }


def main() -> None:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = (repo_root / args.out_dir).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    supports = validate_supports(repo_root)
    rows = normalize_rows(supports)
    statuses = sorted({row["status"] for row in rows})
    summary = {
        "artifact_id": ARTIFACT_ID,
        "generated_at": args.generated_at,
        "chain_row_count": len(rows),
        "support_module_count": len(supports),
        "support_modules": supports,
        "statuses": statuses,
        "terminal_promotion": False,
        "promotion_claims": {
            "maxwell_promoted": False,
            "yang_mills_promoted": False,
            "clay_yang_mills_promoted": False,
            "continuum_mass_gap_promoted": False,
            "terminal_promotion": False,
        },
        "current_terminal_gap": (
            "Finite Hodge targets and selected finite variation calculations are "
            "indexed, but metric Hodge star promotion, physical sourced equations, "
            "self-adjoint Hamiltonian, gauge-invariant spectral gap, uniform lower "
            "bound, and continuum transfer remain open."
        ),
    }

    rows_json = out_dir / f"{ARTIFACT_ID}_rows.json"
    summary_json = out_dir / f"{ARTIFACT_ID}_summary.json"
    rows_csv = out_dir / f"{ARTIFACT_ID}_rows.csv"
    markdown = out_dir / f"{ARTIFACT_ID}.md"
    manifest_json = out_dir / f"{ARTIFACT_ID}_manifest.json"

    write_json(rows_json, rows)
    write_json(summary_json, summary)
    write_csv(rows_csv, rows)
    markdown.write_text(render_markdown(summary, rows), encoding="utf-8")

    manifest = build_manifest(
        repo_root=repo_root,
        out_dir=out_dir,
        generated_at=args.generated_at,
        artifact_paths=[rows_json, summary_json, rows_csv, markdown],
    )
    write_json(manifest_json, manifest)

    print(json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=True))


if __name__ == "__main__":
    main()
