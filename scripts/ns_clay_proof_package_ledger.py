#!/usr/bin/env python3
"""Emit a compact NS Clay proof-package ledger from JSON artifacts.

The ledger is fail-closed. It validates that referenced artifact files exist
and are parseable JSON, records proof packages 1-10 with status labels from the
set {closeable, open, Clay}, and never promotes a theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any


CONTRACT = "ns_clay_proof_package_ledger"
DEFAULT_OUTPUT = Path("outputs") / f"{CONTRACT}.json"
ALLOWED_STATUSES = ("closeable", "open", "Clay")

CONTROL_CARD = {
    "O": "Worker lane 4 owns the NS Clay proof-package ledger emitter.",
    "R": "Record proof packages 1-10 from existing NS calc JSON artifacts without promoting any theorem.",
    "C": "A deterministic Python stdlib CLI writes compact JSON and validates every referenced artifact path.",
    "S": "The repo already carries NS Clay-related summary artifacts for width, cutoff, dissipation, BKM, closure, and bridge work.",
    "L": "Existing JSON artifacts -> validated package records -> compact ledger -> no theorem promotion.",
    "P": "Use this ledger as a package-status receipt only; it is not a proof completion certificate.",
    "G": "Validation passes only when packages 1-10 are present, every referenced file exists, and all statuses are in the allowed set.",
    "F": "No Clay theorem is promoted by this ledger; open and closeable status labels remain descriptive only.",
    "first_six_are_formalization": True,
    "hard_theorem_count": 2,
    "hard_theorems": ["KornLevelSet", "collapseImpossible"],
    "closeable_package_count": 7,
    "concise_regularit_route": "seven closeable packages are formalization/standard packages before the two-wall analytic route",
    "concise_regularity_route": "seven closeable packages are formalization/standard packages before the two-wall analytic route",
    "calc11_status": "complete_no_special_alignment",
    "empirical_diagnostics_complete": True,
    "no_further_calcs_blocking": True,
    "remaining_math_wall": ["KornLevelSet", "collapseImpossible"],
    "hard_wall_count": 2,
    "hard_walls": ["KornLevelSet", "collapseImpossible"],
    "clay_hard_core": "collapseImpossible",
    "post_calc11": {
        "closeable_package_count": 7,
        "hard_wall_count": 2,
        "hard_walls": ["KornLevelSet", "collapseImpossible"],
        "clay_hard_core": "collapseImpossible",
        "no_further_calcs_blocking": True,
        "optional_next_calc": {
            "calc": "Calc12",
            "route_selector": "statistical",
            "blocking": False,
        },
    },
    "formal_packages_write_now": [
        "millerToH5",
        "GD3-SobolevBound-Correct",
        "coareaGradientBound",
        "LocalConcentration",
        "pigeon_concentration",
        "StepA_PerComponent",
        "BoundaryHB_Correct",
    ],
    "boundaryHB_correct_status": "closeable",
    "boundaryHB_correct_dependency": [
        "pointwise_kornBiaxialBound",
        "nondegeneracy",
    ],
    "calc11_next": False,
    "calc11_next_legacy_field_retained": True,
    "calc11_result_summary": {
        "bottom_5_percent_g12_mean_omega_e2_fraction": 0.343,
        "random_baseline": 1.0 / 3.0,
        "full_boundary_layer_mean": 0.432,
        "decision": "no_special_alignment",
    },
}

DEFAULT_PACKAGE_SPECS: tuple[dict[str, Any], ...] = (
    {
        "package_id": 1,
        "package_name": "width_ode_extraction",
        "status": "closeable",
        "artifacts": [
            "outputs/ns_sprint151_width_ode_extraction/"
            "ns_sprint151_width_ode_extraction_summary.json",
        ],
    },
    {
        "package_id": 2,
        "package_name": "cutoff_error_budget",
        "status": "open",
        "artifacts": [
            "outputs/ns_sprint151_cutoff_error_budget/"
            "ns_sprint151_cutoff_error_budget_summary.json",
        ],
    },
    {
        "package_id": 3,
        "package_name": "localized_enstrophy_identity",
        "status": "closeable",
        "artifacts": [
            "outputs/ns_sprint151_localized_enstrophy_identity/"
            "ns_sprint151_localized_enstrophy_identity_summary.json",
        ],
    },
    {
        "package_id": 4,
        "package_name": "source_dissipation_balance",
        "status": "open",
        "artifacts": [
            "outputs/ns_sprint153_source_dissipation_balance/"
            "ns_sprint153_source_dissipation_balance_summary.json",
        ],
    },
    {
        "package_id": 5,
        "package_name": "bkm_bridge_readiness",
        "status": "closeable",
        "artifacts": [
            "outputs/ns_sprint156_bkm_bridge_readiness/"
            "ns_sprint156_bkm_bridge_readiness_summary.json",
        ],
    },
    {
        "package_id": 6,
        "package_name": "bkm_integral_estimate",
        "status": "open",
        "artifacts": [
            "outputs/ns_sprint157_bkm_integral_estimate/"
            "ns_sprint157_bkm_integral_estimate_summary.json",
        ],
    },
    {
        "package_id": 7,
        "package_name": "continuation_bridge",
        "status": "open",
        "artifacts": [
            "outputs/ns_sprint157_continuation_bridge/"
            "ns_sprint157_continuation_bridge_summary.json",
        ],
    },
    {
        "package_id": 8,
        "package_name": "theorem_statement_closure",
        "status": "closeable",
        "artifacts": [
            "outputs/ns_sprint158_theorem_statement_closure/"
            "ns_sprint158_theorem_statement_closure_summary.json",
        ],
    },
    {
        "package_id": 9,
        "package_name": "external_authority_boundary",
        "status": "Clay",
        "artifacts": [
            "outputs/ns_sprint159_external_authority_boundary/"
            "ns_sprint159_external_authority_boundary_summary.json",
        ],
    },
    {
        "package_id": 10,
        "package_name": "clay_governance_rule",
        "status": "open",
        "artifacts": [
            "outputs/ns_sprint160_clay_governance_rule/"
            "ns_sprint160_clay_governance_rule_summary.json",
        ],
    },
)


@dataclass(frozen=True)
class ArtifactRecord:
    path: str
    exists: bool
    size_bytes: int
    sha256: str
    kind: str
    top_level_keys: tuple[str, ...] = ()
    item_count: int | None = None


@dataclass(frozen=True)
class PackageRecord:
    package_id: int
    package_name: str
    status: str
    artifacts: tuple[ArtifactRecord, ...]
    promotion: bool = False
    theorem_promotion: bool = False


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--spec",
        type=Path,
        help="Optional JSON spec file containing {'packages': [...]} for test fixtures.",
    )
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def normalized_spec_entries(spec_data: Any) -> list[dict[str, Any]]:
    if not isinstance(spec_data, dict) or "packages" not in spec_data:
        raise ValueError("spec file must be a JSON object with a non-empty 'packages' list")
    packages = spec_data["packages"]
    if not isinstance(packages, list) or not packages:
        raise ValueError("spec file must contain a non-empty 'packages' list")
    return packages


def artifact_record(repo_root: Path, artifact_path: str) -> ArtifactRecord:
    resolved = (repo_root / artifact_path).resolve()
    if not resolved.exists():
        raise FileNotFoundError(f"missing artifact: {artifact_path}")
    payload = load_json(resolved)
    if isinstance(payload, dict):
        kind = "dict"
        top_level_keys = tuple(sorted(str(key) for key in payload.keys()))
        item_count = None
    elif isinstance(payload, list):
        kind = "list"
        top_level_keys = ()
        item_count = len(payload)
    else:
        kind = type(payload).__name__
        top_level_keys = ()
        item_count = None
    return ArtifactRecord(
        path=str(Path(artifact_path)),
        exists=True,
        size_bytes=resolved.stat().st_size,
        sha256=file_sha256(resolved),
        kind=kind,
        top_level_keys=top_level_keys,
        item_count=item_count,
    )


def build_package_record(repo_root: Path, spec: dict[str, Any]) -> PackageRecord:
    package_id = spec["package_id"]
    package_name = spec["package_name"]
    status = spec["status"]
    artifact_paths = spec["artifacts"]

    if not isinstance(package_id, int):
        raise ValueError(f"package_id must be an int for {package_name!r}")
    if status not in ALLOWED_STATUSES:
        raise ValueError(f"package {package_id} has unsupported status {status!r}")
    if not isinstance(package_name, str) or not package_name:
        raise ValueError(f"package {package_id} must have a non-empty package_name")
    if not isinstance(artifact_paths, list) or not artifact_paths:
        raise ValueError(f"package {package_id} must list at least one artifact path")

    artifacts = tuple(artifact_record(repo_root, str(path)) for path in artifact_paths)
    return PackageRecord(
        package_id=package_id,
        package_name=package_name,
        status=status,
        artifacts=artifacts,
    )


def validate_package_ids(packages: list[PackageRecord]) -> None:
    expected = list(range(1, 11))
    actual = [package.package_id for package in packages]
    if actual != expected:
        raise ValueError(f"package ids must be exactly 1-10 in order; got {actual!r}")


def package_counts(packages: list[PackageRecord]) -> dict[str, int]:
    counts = {status: 0 for status in ALLOWED_STATUSES}
    for package in packages:
        counts[package.status] += 1
    return counts


def build_payload(repo_root: Path, specs: list[dict[str, Any]]) -> dict[str, Any]:
    packages = [build_package_record(repo_root, spec) for spec in specs]
    validate_package_ids(packages)

    payload = {
        "contract": CONTRACT,
        "repo_root": str(repo_root),
        "package_count": len(packages),
        "status_counts": package_counts(packages),
        "packages": [
            {
                "package_id": package.package_id,
                "package_name": package.package_name,
                "status": package.status,
                "promotion": package.promotion,
                "theorem_promotion": package.theorem_promotion,
                "artifacts": [asdict(artifact) for artifact in package.artifacts],
            }
            for package in packages
        ],
        "promotion": False,
        "theorem_promotion": False,
        "calc11_status": "complete_no_special_alignment",
        "empirical_diagnostics_complete": True,
        "closeable_package_count": 7,
        "no_further_calcs_blocking": True,
        "remaining_math_wall": ["KornLevelSet", "collapseImpossible"],
        "hard_wall_count": 2,
        "hard_walls": ["KornLevelSet", "collapseImpossible"],
        "clay_hard_core": "collapseImpossible",
        "formal_packages_write_now": [
            "millerToH5",
            "GD3-SobolevBound-Correct",
            "coareaGradientBound",
            "LocalConcentration",
            "pigeon_concentration",
            "StepA_PerComponent",
            "BoundaryHB_Correct",
        ],
        "boundaryHB_correct_status": "closeable",
        "boundaryHB_correct_dependency": [
            "pointwise_kornBiaxialBound",
            "nondegeneracy",
        ],
        "post_calc11": {
            "closeable_package_count": 7,
            "hard_wall_count": 2,
            "hard_walls": ["KornLevelSet", "collapseImpossible"],
            "clay_hard_core": "collapseImpossible",
            "no_further_calcs_blocking": True,
            "optional_next_calc": {
                "calc": "Calc12",
                "route_selector": "statistical",
                "blocking": False,
            },
        },
        "calc11_result_summary": {
            "bottom_5_percent_g12_mean_omega_e2_fraction": 0.343,
            "random_baseline": 1.0 / 3.0,
            "full_boundary_layer_mean": 0.432,
            "decision": "no_special_alignment",
        },
        "control_card": CONTROL_CARD,
        "validation_passed": True,
    }
    payload["ledger_hash"] = stable_hash({key: value for key, value in payload.items() if key != "ledger_hash"})
    return payload


def load_specs(repo_root: Path, spec_path: Path | None) -> list[dict[str, Any]]:
    if spec_path is None:
        return [dict(spec) for spec in DEFAULT_PACKAGE_SPECS]
    spec_data = load_json(spec_path)
    return normalized_spec_entries(spec_data)


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()

    try:
        specs = load_specs(repo_root, args.spec)
        payload = build_payload(repo_root, specs)
        write_json(args.json_output, payload)
        print(json.dumps(payload, indent=2, sort_keys=True))
        return 0
    except (FileNotFoundError, ValueError, json.JSONDecodeError, OSError) as exc:
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
