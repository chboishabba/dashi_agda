#!/usr/bin/env python3
"""Sprint 133 universal NS regularity strategy classifier.

This deterministic emitter records the six known universal regularity proof
strategy families discussed for 3D incompressible Navier-Stokes.  The output is
an honest strategy map, not a Clay promotion artifact.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint133_universal_strategy_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint133_universal_strategy_classifier")
SUMMARY_NAME = CONTRACT + "_summary.json"
CSV_NAME = CONTRACT + "_rows.csv"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
REPORT_NAME = CONTRACT + ".md"

FIELDNAMES = (
    "strategy_id",
    "name",
    "status_for_full_clay",
    "obstruction_or_gap",
    "programme_relevance",
    "next_calculation",
    "clay_progress_estimate",
)


@dataclass(frozen=True)
class StrategyRow:
    strategy_id: str
    name: str
    status_for_full_clay: str
    obstruction_or_gap: str
    programme_relevance: str
    next_calculation: str
    clay_progress_estimate: str

    def as_row(self) -> dict[str, str]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def build_rows() -> list[dict[str, str]]:
    rows = [
        StrategyRow(
            strategy_id="S1",
            name="A priori estimates",
            status_for_full_clay="exhausted_in_known_energy_enstrophy_class",
            obstruction_or_gap=(
                "The enstrophy estimate dZ/dt <= -nu D + C Z^3 is sharp in "
                "the Ladyzhenskaya class, so energy-only improvement requires "
                "extra structure outside the standard estimate."
            ),
            programme_relevance=(
                "Provides the baseline obstruction against proving Clay by "
                "routine enstrophy closure; supports the shift away from "
                "pure estimate sharpening."
            ),
            next_calculation=(
                "No route-specific calculation currently changes the sharp "
                "energy-enstrophy barrier; use only as a comparison baseline."
            ),
            clay_progress_estimate="approximately_0_percent",
        ),
        StrategyRow(
            strategy_id="S2",
            name="Critical space contraction",
            status_for_full_clay="circular_for_large_data",
            obstruction_or_gap=(
                "Fujita-Kato and Koch-Tataru control small critical data, "
                "while the Escauriaza-Seregin-Sverak L3 blowup criterion says "
                "that a global L3 bound would already close the Clay problem."
            ),
            programme_relevance=(
                "Clarifies why Sprint outputs cannot be promoted through a "
                "critical-norm route unless they produce an energy-derived "
                "large-data Serrin or L3 estimate."
            ),
            next_calculation=(
                "Find an energy-derived bound in a Serrin-Ladyzhenskaya class "
                "or prove that the programme's structural quantities control "
                "a critical norm without smallness."
            ),
            clay_progress_estimate="approximately_0_percent_until_large_data_bound",
        ),
        StrategyRow(
            strategy_id="S3",
            name="Monotone quantity plus comparison",
            status_for_full_clay="most_promising_unexplored_universal_route",
            obstruction_or_gap=(
                "A viable Q[u] must be finite for every smooth finite-energy "
                "datum, monotone along NS flow, and strong enough to bound "
                "BKM-critical vorticity; no such quantity is currently proved."
            ),
            programme_relevance=(
                "Directly uses the obstruction tower's sign audits: the WBF "
                "flux has no global sign, but a vorticity-correlation integral "
                "may exploit alignment geometry in the Constantin-Fefferman "
                "sense."
            ),
            next_calculation=(
                "Differentiate a vorticity-correlation functional Q[u] with "
                "kernel K(x-y)|x-y|^{-alpha}, isolate vortex-stretching, "
                "transport, pressure-free cancellations, and viscous terms, "
                "then test whether stretching has a coercive negative sign."
            ),
            clay_progress_estimate="nonzero_only_if_monotonicity_and_bkm_control_close",
        ),
        StrategyRow(
            strategy_id="S4",
            name="Convexity and duality",
            status_for_full_clay="conceptual_no_concrete_large_data_route",
            obstruction_or_gap=(
                "There is no known convex dual certificate or relaxation whose "
                "large-data free-space NS optimum yields global smoothness."
            ),
            programme_relevance=(
                "Currently peripheral to the repo's WBF and AXS outputs; useful "
                "only if a dual quantity is connected to recorded algebraic "
                "obstructions."
            ),
            next_calculation=(
                "Formulate a concrete dual certificate candidate and check "
                "whether its defect is controlled by energy plus viscosity."
            ),
            clay_progress_estimate="approximately_0_percent_without_candidate_certificate",
        ),
        StrategyRow(
            strategy_id="S5",
            name="Structure theorem",
            status_for_full_clay="live_for_axisymmetric_with_swirl_not_full_clay",
            obstruction_or_gap=(
                "Axisymmetric no-swirl regularity has structure theorems, but "
                "axisymmetric with swirl still needs large-Re beta>0 control, "
                "the beta=0 marginal case, and an exhaustion theorem inside "
                "the symmetry class."
            ),
            programme_relevance=(
                "This is the strongest direct use of CLASS AXS work: Sprint "
                "130-132 artifacts already isolate u1 diffusion, viscous "
                "dominance candidates, and the named no-log Biot-Savart gap."
            ),
            next_calculation=(
                "Pivot to axisymmetric NS with swirl: close large-Re beta>0 "
                "via PDE-level comparison, analyze beta=0 large-scale shear, "
                "and prove axisymmetric-class exhaustion using the reduced "
                "swirl/vorticity system."
            ),
            clay_progress_estimate="positive_for_clay_subcase_zero_for_full_clay_promotion",
        ),
        StrategyRow(
            strategy_id="S6",
            name="Conditional reduction",
            status_for_full_clay="open_no_easier_energy_verifiable_criterion",
            obstruction_or_gap=(
                "Known continuation criteria such as Serrin and BKM are not "
                "verified from energy alone; a new criterion must be both "
                "strictly weaker to verify and strong enough to continue "
                "smooth solutions."
            ),
            programme_relevance=(
                "Could absorb WBF/AXS obstructions if they imply a universal "
                "regularity criterion, but current outputs remain route-specific."
            ),
            next_calculation=(
                "Search for a criterion below Serrin/BKM whose hypothesis is "
                "controlled by energy, viscosity, and a programme structural "
                "quantity already emitted in Sprint 130-132 surfaces."
            ),
            clay_progress_estimate="approximately_0_percent_until_new_criterion",
        ),
    ]
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, str]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDNAMES)
        writer.writeheader()
        writer.writerows(rows)


def fmt_bool(value: bool) -> str:
    return str(value).lower()


def markdown_table(rows: list[dict[str, str]]) -> str:
    headers = (
        "Strategy",
        "Name",
        "Status",
        "Gap",
        "Next Calculation",
        "Clay Progress",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append(
            "| "
            + " | ".join(
                (
                    f"`{row['strategy_id']}`",
                    row["name"],
                    f"`{row['status_for_full_clay']}`",
                    row["obstruction_or_gap"],
                    row["next_calculation"],
                    f"`{row['clay_progress_estimate']}`",
                )
            )
            + " |"
        )
    return "\n".join(lines)


def build_summary(rows: list[dict[str, str]]) -> dict[str, Any]:
    status_counts: dict[str, int] = {}
    for row in rows:
        status = row["status_for_full_clay"]
        status_counts[status] = status_counts.get(status, 0) + 1

    selected_next_strategy = "S5"
    universal_candidate_strategy = "S3"
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "strategy_ids": [row["strategy_id"] for row in rows],
        "required_fields": list(FIELDNAMES),
        "status_counts": status_counts,
        "selected_clay_adjacent_target": "axisymmetric NS with swirl",
        "selected_next_strategy": selected_next_strategy,
        "universal_candidate_strategy": universal_candidate_strategy,
        "highest_alpha_next_calculations": [
            "AxisymmetricWithSwirlLargeReBetaPositivePDEComparison",
            "AxisymmetricMarginalBetaZeroShearAnalysis",
            "AxisymmetricClassExhaustionTheorem",
            "VorticityCorrelationMonotonicityDerivative",
            "SerrinEnergyConditionalReductionSearch",
            "ConvexDualCertificateFeasibilityCheck",
        ],
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
        "exit_reason": (
            "classified six universal proof strategies and selected the "
            "axisymmetric-with-swirl structure-theorem route as the strongest "
            "Clay-adjacent continuation without promoting full Clay regularity"
        ),
        "control_card": {
            "O": (
                "Worker 1 owns only the Sprint133 universal strategy classifier "
                "script and generated output directory."
            ),
            "R": (
                "Encode six universal regularity proof strategies with required "
                "row fields and explicit Clay non-promotion flags."
            ),
            "C": (
                "Deterministic Python emitter writes CSV rows, JSON rows, JSON "
                "summary, and Markdown report."
            ),
            "S": (
                "Full Clay remains unsolved; route-specific Sprint 130-132 work "
                "most directly supports the axisymmetric-with-swirl subcase."
            ),
            "L": (
                "Progress lattice: classify strategies -> select tractable "
                "Clay-adjacent target -> keep full Clay promotion false."
            ),
            "P": (
                "Treat structure theorem for axisymmetric NS with swirl as the "
                "next significant finite-scope target; keep monotone quantity "
                "as the only plausible universal positive route."
            ),
            "G": (
                "Promotion requires universal smooth finite-energy regularity; "
                "this artifact explicitly does not claim that."
            ),
            "F": (
                "Remaining gap is a universal argument or a finite exhaustion "
                "inside a symmetry class, not another route-specific receipt."
            ),
        },
    }


def render_markdown(summary: dict[str, Any], rows: list[dict[str, str]]) -> str:
    lines = [
        "# NS Sprint 133 Universal Strategy Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Row count: `{summary['row_count']}`",
        f"- Selected Clay-adjacent target: `{summary['selected_clay_adjacent_target']}`",
        f"- Selected next strategy: `{summary['selected_next_strategy']}`",
        f"- Universal candidate strategy: `{summary['universal_candidate_strategy']}`",
        f"- Full Clay NS solved: `{fmt_bool(summary['full_clay_ns_solved'])}`",
        f"- Clay Navier-Stokes promoted: `{fmt_bool(summary['clay_navier_stokes_promoted'])}`",
        f"- Complete: `{fmt_bool(summary['complete'])}`",
        f"- Exit code: `{summary['exit_code']}`",
        "",
        "## Rows",
        "",
        markdown_table(rows),
        "",
        "## Highest-Alpha Next Calculations",
        "",
    ]
    for item in summary["highest_alpha_next_calculations"]:
        lines.append(f"- `{item}`")
    lines.extend(["", "## Control Card", ""])
    for key, value in summary["control_card"].items():
        lines.append(f"- {key}: {value}")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)

    write_csv(out_dir / CSV_NAME, rows)
    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    (out_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")

    print(
        json.dumps(
            {
                "contract": summary["contract"],
                "row_count": summary["row_count"],
                "selected_clay_adjacent_target": summary["selected_clay_adjacent_target"],
                "selected_next_strategy": summary["selected_next_strategy"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
                "complete": summary["complete"],
                "exit_code": summary["exit_code"],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
