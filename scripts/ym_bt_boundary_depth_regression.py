#!/usr/bin/env python3
"""Depth-regression wrapper for the finite BT-tree spectral-gap harness.

This is a diagnostic runner, not a Yang-Mills proof.  It calls
``scripts/ym_bt_tree_spectral_gap_harness.py`` with a deeper p/depth sweep,
parses the emitted JSON, and summarizes which boundary conventions look stable
under depth growth versus finite-size-sensitive.
"""

from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


DEFAULT_PS = (2, 3, 5, 7)
DEFAULT_DEPTHS = tuple(range(2, 11))
DEFAULT_BOUNDARIES = (
    "induced",
    "full-degree",
    "induced-root-anchored",
    "full-degree-root-anchored",
)
DEFAULT_LAPLACIANS = ("combinatorial", "normalized")
DEFAULT_MAX_NODES = 12000
DEFAULT_OUT = Path("outputs/ym_bt_boundary_depth_regression_summary.json")
STABLE_RATIO_MIN = 0.50
COLLAPSED_RATIO_MAX = 0.10
SENSITIVE_DECAY_RATIO_MAX = 0.55
FLAT_SLOPE_MAX = 0.08

ADMISSIBLE_CANDIDATE_BOUNDARIES = frozenset(
    {
        "full-degree",
        "full-degree-root-anchored",
    }
)
INADMISSIBLE_CURRENT_GAP_CARRIER_BOUNDARIES = frozenset(
    {
        "induced",
        "induced-root-anchored",
    }
)


@dataclass(frozen=True)
class RegressionRow:
    p: int
    boundary: str
    laplacian: str
    sample_count: int
    depths: list[int]
    gaps: list[float]
    ratios: list[float]
    deepest_depth: int | None
    deepest_vertex_count: int | None
    deepest_gap: float | None
    deepest_ratio_to_reference: float | None
    ratio_first_to_last: float | None
    gap_first_to_last: float | None
    ratio_slope_per_depth: float | None
    log_gap_slope_per_depth: float | None
    monotone_gap_decrease: bool
    monotone_ratio_decrease: bool
    classification: str
    boundary_admissibility: str
    theorem_precondition_status: str
    rationale: str


@dataclass(frozen=True)
class BoundaryComparison:
    p: int
    laplacian: str
    induced_boundary: str
    full_degree_boundary: str
    induced_deepest_ratio: float | None
    full_degree_deepest_ratio: float | None
    full_over_induced_ratio: float | None
    classification: str
    rationale: str


@dataclass(frozen=True)
class BoundaryAdmissibilityRow:
    boundary: str
    admissibility: str
    accepted_as_current_gap_carrier: bool
    theorem_precondition_status: str
    rationale: str
    required_followups: list[str]


def parse_int_csv(raw: str) -> tuple[int, ...]:
    values = tuple(int(part.strip()) for part in raw.split(",") if part.strip())
    if not values:
        raise argparse.ArgumentTypeError("expected at least one integer")
    return values


def parse_str_csv(raw: str) -> tuple[str, ...]:
    values = tuple(part.strip() for part in raw.split(",") if part.strip())
    if not values:
        raise argparse.ArgumentTypeError("expected at least one value")
    return values


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--p", dest="ps", type=parse_int_csv, default=DEFAULT_PS)
    parser.add_argument("--depths", type=parse_int_csv, default=DEFAULT_DEPTHS)
    parser.add_argument("--boundary", type=parse_str_csv, default=DEFAULT_BOUNDARIES)
    parser.add_argument("--laplacian", type=parse_str_csv, default=DEFAULT_LAPLACIANS)
    parser.add_argument("--max-nodes", type=int, default=DEFAULT_MAX_NODES)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--harness-out", type=Path, default=None)
    parser.add_argument("--print-json", action="store_true")
    return parser.parse_args()


def csv(values: tuple[int, ...] | tuple[str, ...]) -> str:
    return ",".join(str(value) for value in values)


def linear_slope(xs: list[int], ys: list[float]) -> float | None:
    if len(xs) < 2 or len(ys) < 2:
        return None
    mean_x = sum(xs) / len(xs)
    mean_y = sum(ys) / len(ys)
    variance = sum((x - mean_x) ** 2 for x in xs)
    if variance == 0.0:
        return None
    covariance = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys, strict=True))
    return covariance / variance


def strictly_nonincreasing(values: list[float], tolerance: float = 1e-10) -> bool:
    return all(next_value <= value + tolerance for value, next_value in zip(values, values[1:]))


def classify_boundary_admissibility(boundary: str) -> BoundaryAdmissibilityRow:
    if boundary in ADMISSIBLE_CANDIDATE_BOUNDARIES:
        return BoundaryAdmissibilityRow(
            boundary=boundary,
            admissibility="admissible-candidate",
            accepted_as_current_gap_carrier=True,
            theorem_precondition_status="candidate-satisfied-not-promoted",
            rationale=(
                "Full-degree/killing-style truncation is the current admissible "
                "candidate because missing exterior tree edges remain charged."
            ),
            required_followups=[
                "FiniteGaugeQuotientCarrierConstruction",
                "HamiltonianDominatesDefectPlusHolonomy",
                "ReflectionPositiveTransferMatrix",
                "BruhatTitsToOSLatticeTransfer",
                "ContinuumTransferNoSpectralPollution",
            ],
        )

    if boundary in INADMISSIBLE_CURRENT_GAP_CARRIER_BOUNDARIES:
        return BoundaryAdmissibilityRow(
            boundary=boundary,
            admissibility="inadmissible-current-gap-carrier",
            accepted_as_current_gap_carrier=False,
            theorem_precondition_status="violated",
            rationale=(
                "Induced finite-ball truncation is rejected for the current gap "
                "route because finite leaves do not pay for missing exterior edges."
            ),
            required_followups=[
                "Do not use induced finite balls as the theorem carrier for the current YM route.",
                "Keep induced rows only as negative-control diagnostics.",
            ],
        )

    return BoundaryAdmissibilityRow(
        boundary=boundary,
        admissibility="unknown-boundary-convention",
        accepted_as_current_gap_carrier=False,
        theorem_precondition_status="unknown",
        rationale="Boundary convention is not recognized by the admissibility policy.",
        required_followups=[
            "Classify the convention before using it in Hamiltonian domination or OS transfer.",
        ],
    )


def classify(boundary: str, ratios: list[float], gaps: list[float], ratio_slope: float | None) -> tuple[str, str]:
    if len(ratios) < 2 or len(gaps) < 2:
        return "insufficient-depth-data", "Fewer than two computed depths survived the max-node cap."

    deepest_ratio = ratios[-1]
    first_ratio = ratios[0]
    ratio_first_to_last = None if first_ratio == 0.0 else deepest_ratio / first_ratio
    monotone_gap_decrease = strictly_nonincreasing(gaps)

    if deepest_ratio <= COLLAPSED_RATIO_MAX:
        return (
            "apparent-gap-collapse",
            f"Deepest ratio {deepest_ratio:.4g} is below collapse threshold {COLLAPSED_RATIO_MAX:.4g}.",
        )

    if boundary.startswith("induced") and monotone_gap_decrease:
        if ratio_first_to_last is not None and ratio_first_to_last <= SENSITIVE_DECAY_RATIO_MAX:
            return (
                "finite-size-sensitive-collapse-trend",
                "Induced convention shows monotone depth decay and a large first-to-last ratio loss.",
            )
        return (
            "finite-size-sensitive-decreasing",
            "Induced convention shows monotone depth decay; deeper truncations remain material.",
        )

    if boundary.startswith("full-degree") and deepest_ratio >= STABLE_RATIO_MIN:
        if ratio_slope is not None and abs(ratio_slope) <= FLAT_SLOPE_MAX:
            return (
                "stable-gap-preserving",
                "Full-degree/killing convention keeps a substantial reference ratio with a flat late trend.",
            )
        return (
            "gap-preserving-with-depth-drift",
            "Full-degree/killing convention keeps a substantial ratio but the trend is still moving.",
        )

    if deepest_ratio >= STABLE_RATIO_MIN:
        return (
            "borderline-stable",
            "Deepest ratio is substantial, but the boundary convention or slope prevents stable classification.",
        )

    return (
        "borderline-finite-size-sensitive",
        "Deepest ratio is between collapse and stable thresholds.",
    )


def build_regressions(rows: list[dict[str, Any]]) -> list[RegressionRow]:
    grouped: dict[tuple[int, str, str], list[dict[str, Any]]] = {}
    for row in rows:
        if row.get("status") != "computed":
            continue
        if row.get("first_nonzero_eigenvalue") is None or row.get("ratio_to_reference") is None:
            continue
        key = (int(row["p"]), str(row["boundary"]), str(row["laplacian"]))
        grouped.setdefault(key, []).append(row)

    regressions: list[RegressionRow] = []
    for (p, boundary, laplacian), group in sorted(grouped.items()):
        ordered = sorted(group, key=lambda item: int(item["depth"]))
        depths = [int(item["depth"]) for item in ordered]
        gaps = [float(item["first_nonzero_eigenvalue"]) for item in ordered]
        ratios = [float(item["ratio_to_reference"]) for item in ordered]
        ratio_slope = linear_slope(depths, ratios)
        positive_gap_pairs = [(depth, gap) for depth, gap in zip(depths, gaps, strict=True) if gap > 0.0]
        log_gap_slope = linear_slope(
            [depth for depth, _ in positive_gap_pairs],
            [math.log(gap) for _, gap in positive_gap_pairs],
        )
        classification, rationale = classify(boundary, ratios, gaps, ratio_slope)
        admissibility = classify_boundary_admissibility(boundary)
        first_ratio = ratios[0]
        first_gap = gaps[0]
        regressions.append(
            RegressionRow(
                p=p,
                boundary=boundary,
                laplacian=laplacian,
                sample_count=len(ordered),
                depths=depths,
                gaps=gaps,
                ratios=ratios,
                deepest_depth=depths[-1] if depths else None,
                deepest_vertex_count=int(ordered[-1]["vertex_count"]) if ordered else None,
                deepest_gap=gaps[-1] if gaps else None,
                deepest_ratio_to_reference=ratios[-1] if ratios else None,
                ratio_first_to_last=None if first_ratio == 0.0 else ratios[-1] / first_ratio,
                gap_first_to_last=None if first_gap == 0.0 else gaps[-1] / first_gap,
                ratio_slope_per_depth=ratio_slope,
                log_gap_slope_per_depth=log_gap_slope,
                monotone_gap_decrease=strictly_nonincreasing(gaps),
                monotone_ratio_decrease=strictly_nonincreasing(ratios),
                classification=classification,
                boundary_admissibility=admissibility.admissibility,
                theorem_precondition_status=admissibility.theorem_precondition_status,
                rationale=rationale,
            )
        )
    return regressions


def compare_boundaries(regressions: list[RegressionRow]) -> list[BoundaryComparison]:
    by_key = {(item.p, item.boundary, item.laplacian): item for item in regressions}
    comparisons: list[BoundaryComparison] = []
    boundary_pairs = (
        ("induced", "full-degree"),
        ("induced-root-anchored", "full-degree-root-anchored"),
    )
    keys = sorted({(item.p, item.laplacian) for item in regressions})
    for p, laplacian in keys:
        for induced_boundary, full_boundary in boundary_pairs:
            induced = by_key.get((p, induced_boundary, laplacian))
            full = by_key.get((p, full_boundary, laplacian))
            if induced is None or full is None:
                continue
            induced_ratio = induced.deepest_ratio_to_reference
            full_ratio = full.deepest_ratio_to_reference
            full_over_induced = None
            if induced_ratio is not None and induced_ratio > 0.0 and full_ratio is not None:
                full_over_induced = full_ratio / induced_ratio

            if induced.classification.startswith("finite-size") and full.classification.startswith(("stable", "gap-preserving")):
                classification = "boundary-convention-separates-collapse-from-gap"
                rationale = "Induced finite balls decay while full-degree/killing truncations retain a substantial gap."
            elif full.classification.startswith(("stable", "gap-preserving")):
                classification = "full-degree-more-stable"
                rationale = "Full-degree/killing truncation is stable or gap-preserving relative to induced."
            elif induced.classification == full.classification:
                classification = "same-classification"
                rationale = "Both boundary conventions landed in the same regime."
            else:
                classification = "mixed-or-inconclusive"
                rationale = "Boundary comparison is not decisive at the selected depth cap."

            comparisons.append(
                BoundaryComparison(
                    p=p,
                    laplacian=laplacian,
                    induced_boundary=induced_boundary,
                    full_degree_boundary=full_boundary,
                    induced_deepest_ratio=induced_ratio,
                    full_degree_deepest_ratio=full_ratio,
                    full_over_induced_ratio=full_over_induced,
                    classification=classification,
                    rationale=rationale,
                )
            )
    return comparisons


def build_boundary_admissibility_policy(boundaries: tuple[str, ...]) -> dict[str, Any]:
    rows = [classify_boundary_admissibility(boundary) for boundary in sorted(set(boundaries))]
    counts: dict[str, int] = {}
    for row in rows:
        counts[row.admissibility] = counts.get(row.admissibility, 0) + 1
    accepted = [row.boundary for row in rows if row.accepted_as_current_gap_carrier]
    rejected = [
        row.boundary
        for row in rows
        if row.admissibility == "inadmissible-current-gap-carrier"
    ]
    unknown = [row.boundary for row in rows if row.admissibility == "unknown-boundary-convention"]

    if accepted and not unknown:
        status = "explicit-admissible-candidate-present"
    elif accepted and unknown:
        status = "candidate-present-with-unclassified-boundaries"
    elif unknown:
        status = "unclassified-boundaries-present"
    else:
        status = "no-admissible-candidate-boundary-selected"

    return {
        "status": status,
        "promotion": False,
        "ym_mass_gap_promoted": False,
        "clay_promoted": False,
        "accepted_current_gap_carrier_boundaries": accepted,
        "rejected_current_gap_carrier_boundaries": rejected,
        "unknown_boundaries": unknown,
        "classification_counts": counts,
        "policy_rows": [asdict(row) for row in rows],
        "precondition_statement": (
            "Current finite BT/YM route requires a full-degree/killing-style "
            "boundary convention before attempting finite gauge quotient or "
            "Hamiltonian-domination transfer. This is a theorem precondition, "
            "not a mass-gap proof."
        ),
    }


def build_theorem_precondition_status(regressions: list[RegressionRow], boundaries: tuple[str, ...]) -> dict[str, Any]:
    policy = build_boundary_admissibility_policy(boundaries)
    row_counts: dict[str, int] = {}
    for row in regressions:
        row_counts[row.theorem_precondition_status] = row_counts.get(row.theorem_precondition_status, 0) + 1

    admissible_rows = [
        row
        for row in regressions
        if row.boundary_admissibility == "admissible-candidate"
    ]
    inadmissible_rows = [
        row
        for row in regressions
        if row.boundary_admissibility == "inadmissible-current-gap-carrier"
    ]
    admissible_gap_preserving_rows = [
        row
        for row in admissible_rows
        if row.classification.startswith(("stable", "gap-preserving"))
        or row.classification == "borderline-stable"
    ]
    inadmissible_collapse_rows = [
        row
        for row in inadmissible_rows
        if row.classification.startswith(("finite-size", "apparent-gap-collapse"))
    ]

    if not admissible_rows:
        status = "failed-no-admissible-boundary-candidate"
        rationale = "No full-degree/killing-style boundary rows were selected."
    elif not admissible_gap_preserving_rows:
        status = "failed-admissible-candidate-lacks-gap-signal"
        rationale = "Selected admissible candidate rows did not retain the finite-tree gap signal."
    elif inadmissible_rows and not inadmissible_collapse_rows:
        status = "mixed-negative-controls-not-decisive"
        rationale = "Admissible candidates retain signal, but induced negative controls did not clearly decay."
    else:
        status = "candidate-precondition-supported-by-regression"
        rationale = (
            "Full-degree/killing-style rows retain a candidate gap signal while "
            "induced rows are rejected or act as collapse-sensitive negative controls."
        )

    return {
        "status": status,
        "rationale": rationale,
        "promotion": False,
        "ym_mass_gap_promoted": False,
        "clay_promoted": False,
        "row_status_counts": row_counts,
        "admissible_row_count": len(admissible_rows),
        "admissible_gap_preserving_row_count": len(admissible_gap_preserving_rows),
        "inadmissible_row_count": len(inadmissible_rows),
        "inadmissible_collapse_row_count": len(inadmissible_collapse_rows),
        "blocked_downstream_theorems": [
            "FiniteGaugeQuotientCarrierConstruction",
            "HamiltonianDominatesDefectPlusHolonomy",
            "ReflectionPositiveTransferMatrix",
            "BruhatTitsToOSLatticeTransfer",
            "ContinuumTransferNoSpectralPollution",
            "ClayYangMillsAuthorityTranslation",
        ],
        "boundary_admissibility_policy": policy,
    }


def run_base_harness(args: argparse.Namespace, harness_out: Path) -> dict[str, Any]:
    repo_root = Path(__file__).resolve().parents[1]
    harness = repo_root / "scripts" / "ym_bt_tree_spectral_gap_harness.py"
    command = [
        sys.executable,
        str(harness),
        "--p",
        csv(args.ps),
        "--depths",
        csv(args.depths),
        "--boundary",
        csv(args.boundary),
        "--laplacian",
        csv(args.laplacian),
        "--max-nodes",
        str(args.max_nodes),
        "--out",
        str(harness_out),
    ]
    completed = subprocess.run(command, cwd=repo_root, check=True, capture_output=True, text=True)
    return {
        "command": command,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
        "summary": json.loads(harness_out.read_text(encoding="utf-8")),
    }


def build_summary(args: argparse.Namespace, harness_result: dict[str, Any]) -> dict[str, Any]:
    base_summary = harness_result["summary"]
    regressions = build_regressions(list(base_summary.get("rows", [])))
    comparisons = compare_boundaries(regressions)
    theorem_precondition_status = build_theorem_precondition_status(regressions, args.boundary)
    classification_counts: dict[str, int] = {}
    for item in regressions:
        classification_counts[item.classification] = classification_counts.get(item.classification, 0) + 1
    comparison_counts: dict[str, int] = {}
    for item in comparisons:
        comparison_counts[item.classification] = comparison_counts.get(item.classification, 0) + 1

    return {
        "control": {
            "O": "YM BT boundary depth-regression diagnostic runner.",
            "R": "Run deeper finite regular-tree spectral-gap sweeps and classify depth/boundary stability.",
            "C": "scripts/ym_bt_boundary_depth_regression.py wrapping scripts/ym_bt_tree_spectral_gap_harness.py.",
            "S": "Numerical finite-tree evidence only; boundary effects remain model-dependent.",
            "L": "base harness rows -> depth trends -> induced/full-degree comparison -> fail-closed classification",
            "P": "Treat full-degree/killing stability and induced collapse as boundary-convention evidence, not YM proof.",
            "G": "promotion=false; clay_promoted=false; ym_mass_gap_promoted=false.",
            "F": "Does not prove gauge quotient, holonomy action, Hamiltonian domination, OS transfer, or continuum gap.",
        },
        "parameters": {
            "p": list(args.ps),
            "depths": list(args.depths),
            "boundary": list(args.boundary),
            "laplacian": list(args.laplacian),
            "max_nodes": args.max_nodes,
        },
        "thresholds": {
            "stable_ratio_min": STABLE_RATIO_MIN,
            "collapsed_ratio_max": COLLAPSED_RATIO_MAX,
            "sensitive_decay_ratio_max": SENSITIVE_DECAY_RATIO_MAX,
            "flat_slope_max": FLAT_SLOPE_MAX,
        },
        "promotion": False,
        "clay_promoted": False,
        "ym_mass_gap_promoted": False,
        "base_harness_command": harness_result["command"],
        "base_harness_stdout_tail": harness_result["stdout"][-4000:],
        "base_harness_stderr_tail": harness_result["stderr"][-4000:],
        "base_classification_counts": base_summary.get("classification_counts", {}),
        "regression_classification_counts": classification_counts,
        "comparison_classification_counts": comparison_counts,
        "theorem_precondition_status": theorem_precondition_status,
        "boundary_admissibility_policy": theorem_precondition_status["boundary_admissibility_policy"],
        "regressions": [asdict(item) for item in regressions],
        "boundary_comparisons": [asdict(item) for item in comparisons],
        "skipped": base_summary.get("skipped", []),
    }


def print_table(summary: dict[str, Any]) -> None:
    print("YM BT boundary depth regression")
    print(f"promotion={summary['promotion']} clay_promoted={summary['clay_promoted']}")
    theorem_status = summary["theorem_precondition_status"]
    print(f"theorem_precondition_status={theorem_status['status']}")
    print(f"theorem_precondition_rationale={theorem_status['rationale']}")
    print(f"regression classifications: {summary['regression_classification_counts']}")
    print(f"boundary comparisons: {summary['comparison_classification_counts']}")
    print(
        "boundary admissibility: "
        f"{summary['boundary_admissibility_policy']['classification_counts']}"
    )
    skipped = summary.get("skipped", [])
    if skipped:
        print(f"skipped by max-node cap: {len(skipped)}")
    print()
    print("p boundary                   laplacian      depth ratio_last  slope      class")
    print("-" * 102)
    for row in summary["regressions"]:
        ratio = row["deepest_ratio_to_reference"]
        slope = row["ratio_slope_per_depth"]
        ratio_text = "NA" if ratio is None else f"{ratio:.6g}"
        slope_text = "NA" if slope is None else f"{slope:.4g}"
        print(
            f"{row['p']:<2} {row['boundary']:<26} {row['laplacian']:<14} "
            f"{str(row['deepest_depth']):>5} {ratio_text:>10} {slope_text:>10}  "
            f"{row['classification']}"
        )


def main() -> int:
    args = parse_args()
    if args.max_nodes <= 0:
        raise SystemExit("--max-nodes must be positive")

    if args.harness_out is not None:
        harness_out = args.harness_out
        harness_out.parent.mkdir(parents=True, exist_ok=True)
        harness_result = run_base_harness(args, harness_out)
    else:
        with tempfile.TemporaryDirectory(prefix="ym_bt_boundary_regression_") as tmpdir:
            harness_out = Path(tmpdir) / "base_harness_summary.json"
            harness_result = run_base_harness(args, harness_out)

    summary = build_summary(args, harness_result)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if args.print_json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print_table(summary)
        print()
        print(f"wrote summary: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
