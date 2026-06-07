#!/usr/bin/env python3
"""Sprint 132 NS mechanism-exhaustion audit.

This deterministic emitter records why four attempted global-exhaustion
routes do not promote the Sprint130/131 obstruction tower into full Clay
Navier-Stokes global regularity.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint132_mechanism_exhaustion_audit"
DEFAULT_OUT_DIR = Path("outputs/ns_sprint132_mechanism_exhaustion_audit")
ROWS_NAME = f"{CONTRACT}_rows.json"
SUMMARY_NAME = f"{CONTRACT}_summary.json"
REPORT_NAME = f"{CONTRACT}.md"

ROUTE_SCOPE = "obstruction tower to Clay global regularity"
OBSTRUCTION_TOWER = (
    "Sprint130/131 Hou-Luo viscous route obstruction tower: U1 maximum "
    "principle, source upper bound, localized viscous comparison, and "
    "AxisymmetricHouLuoNSViscousDominanceObstruction"
)


@dataclass(frozen=True)
class ExhaustionRow:
    route_id: str
    route_name: str
    route_scope: str
    attempted_bridge: str
    obstruction_tower_input: str
    fails_as_global_exhaustion_route: bool
    failure_class: str
    why_it_fails: str
    route_specific_obstruction_theorem_possible: bool
    mechanism_exhaustion_closed: bool
    structural_gap: bool
    missing_calculation: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    next_valid_claim: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        ExhaustionRow(
            route_id="enumeration",
            route_name="Enumeration of known obstruction mechanisms",
            route_scope=ROUTE_SCOPE,
            attempted_bridge=(
                "list all mechanisms represented in the obstruction tower and "
                "treat the list as exhaustive for all smooth finite-energy NS flows"
            ),
            obstruction_tower_input=OBSTRUCTION_TOWER,
            fails_as_global_exhaustion_route=True,
            failure_class="non_exhaustive_model_class",
            why_it_fails=(
                "The tower obstructs a structured Hou-Luo near-axis route, but "
                "enumerating that tower does not classify every possible "
                "three-dimensional concentration, cascade, geometry, boundary, "
                "or pressure scenario. A finite route ledger is not a theorem "
                "that every Clay-counterexample trajectory must enter one listed "
                "mechanism."
            ),
            route_specific_obstruction_theorem_possible=True,
            mechanism_exhaustion_closed=False,
            structural_gap=True,
            missing_calculation=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            next_valid_claim=(
                "record route-specific exclusions and keep the global mechanism "
                "classification open"
            ),
        ),
        ExhaustionRow(
            route_id="lyapunov_functional",
            route_name="Lyapunov functional exhaustion",
            route_scope=ROUTE_SCOPE,
            attempted_bridge=(
                "upgrade local viscous dominance into a global monotone "
                "functional controlling every critical norm up to arbitrary time"
            ),
            obstruction_tower_input=OBSTRUCTION_TOWER,
            fails_as_global_exhaustion_route=True,
            failure_class="no_global_coercive_monotone_quantity",
            why_it_fails=(
                "The tower supplies localized sign and scaling information near "
                "the Hou-Luo ansatz. It does not construct a coercive Lyapunov "
                "functional equivalent to a Clay-critical regularity norm, nor "
                "does it prove monotonicity after pressure, transport, vortex "
                "stretching, and nonlocal energy transfer are included globally."
            ),
            route_specific_obstruction_theorem_possible=True,
            mechanism_exhaustion_closed=False,
            structural_gap=True,
            missing_calculation=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            next_valid_claim=(
                "use localized viscous dominance only inside its stated route "
                "scope"
            ),
        ),
        ExhaustionRow(
            route_id="comparison_principle",
            route_name="Comparison principle exhaustion",
            route_scope=ROUTE_SCOPE,
            attempted_bridge=(
                "turn the U1 maximum principle and localized viscous lower "
                "comparison into an order-preserving comparison for full 3D NS"
            ),
            obstruction_tower_input=OBSTRUCTION_TOWER,
            fails_as_global_exhaustion_route=True,
            failure_class="order_structure_not_available",
            why_it_fails=(
                "The U1 receipt has a scalar divergence-form maximum principle "
                "inside the axisymmetric route, but the full Navier-Stokes "
                "system has nonlocal pressure and vortex-stretching couplings "
                "with no global positive cone that orders vector solutions. "
                "The comparison cannot cover arbitrary 3D data or all possible "
                "singularity geometries."
            ),
            route_specific_obstruction_theorem_possible=True,
            mechanism_exhaustion_closed=False,
            structural_gap=True,
            missing_calculation=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            next_valid_claim=(
                "retain comparison claims only for the scalar or localized "
                "quantities where the sign structure is proved"
            ),
        ),
        ExhaustionRow(
            route_id="probabilistic",
            route_name="Probabilistic or generic exhaustion",
            route_scope=ROUTE_SCOPE,
            attempted_bridge=(
                "argue that the obstruction tower rules out all blowup-relevant "
                "mechanisms almost surely or generically, then infer deterministic "
                "Clay regularity"
            ),
            obstruction_tower_input=OBSTRUCTION_TOWER,
            fails_as_global_exhaustion_route=True,
            failure_class="generic_does_not_imply_deterministic_universal",
            why_it_fails=(
                "Clay regularity is a deterministic universal statement for all "
                "smooth finite-energy initial data. A probabilistic or generic "
                "exclusion would still leave exceptional trajectories unless it "
                "is upgraded to a deterministic covering theorem; the obstruction "
                "tower contains no such measure-to-all-data promotion."
            ),
            route_specific_obstruction_theorem_possible=True,
            mechanism_exhaustion_closed=False,
            structural_gap=True,
            missing_calculation=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            next_valid_claim=(
                "separate probabilistic or generic evidence from a universal "
                "Clay conclusion"
            ),
        ),
    ]
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def fmt_bool(value: bool) -> str:
    return str(value).lower()


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "route",
        "failure class",
        "fails",
        "structural gap",
        "missing calculation",
        "Clay promoted",
    )
    keys = (
        "route_id",
        "failure_class",
        "fails_as_global_exhaustion_route",
        "structural_gap",
        "missing_calculation",
        "clay_navier_stokes_promoted",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append(
            "| "
            + " | ".join(
                fmt_bool(row[key]) if isinstance(row[key], bool) else f"`{row[key]}`"
                for key in keys
            )
            + " |"
        )
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "contract": CONTRACT,
        "route_scope": ROUTE_SCOPE,
        "obstruction_tower": OBSTRUCTION_TOWER,
        "route_count": len(rows),
        "routes": [row["route_id"] for row in rows],
        "all_routes_fail_as_global_exhaustion": all(
            row["fails_as_global_exhaustion_route"] for row in rows
        ),
        "failed_global_exhaustion_routes": [row["route_id"] for row in rows],
        "mechanism_exhaustion_closed": False,
        "structural_gap": True,
        "missing_calculation": False,
        "route_specific_obstruction_theorem_possible": True,
        "full_clay_ns_solved": False,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
        "exit_reason": (
            "four global-exhaustion routes are recorded as structurally "
            "insufficient to promote the obstruction tower to full Clay "
            "Navier-Stokes regularity"
        ),
        "control_card": {
            "O": "Worker 2 owns only the Sprint132 mechanism-exhaustion audit script and output directory",
            "R": "encode enumeration, Lyapunov functional, comparison principle, and probabilistic global-exhaustion failures",
            "C": "deterministic Python emitter writing rows JSON, summary JSON, and Markdown",
            "S": "the obstruction tower remains route-specific support, not a global classification of all NS dynamics",
            "L": "each row records a structural route gap rather than a missing numeric calculation",
            "P": "route-specific obstruction theorems remain possible while mechanism exhaustion stays open",
            "G": "exit code is 0 with complete audit artifacts and Clay promotion held false",
            "F": "do not infer full Clay Navier-Stokes regularity from this audit",
        },
    }


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 132 Mechanism Exhaustion Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Route scope: `{summary['route_scope']}`",
        f"- Route count: `{summary['route_count']}`",
        f"- Mechanism exhaustion closed: `{fmt_bool(summary['mechanism_exhaustion_closed'])}`",
        f"- Structural gap: `{fmt_bool(summary['structural_gap'])}`",
        f"- Missing calculation: `{fmt_bool(summary['missing_calculation'])}`",
        (
            "- Route-specific obstruction theorem possible: "
            f"`{fmt_bool(summary['route_specific_obstruction_theorem_possible'])}`"
        ),
        f"- Full Clay NS solved: `{fmt_bool(summary['full_clay_ns_solved'])}`",
        f"- Clay Navier-Stokes promoted: `{fmt_bool(summary['clay_navier_stokes_promoted'])}`",
        f"- Complete: `{fmt_bool(summary['complete'])}`",
        f"- Exit code: `{summary['exit_code']}`",
        "",
        "## Obstruction Tower",
        "",
        summary["obstruction_tower"],
        "",
        "## Route Ledger",
        "",
        markdown_table(rows),
        "",
        "## Failure Notes",
        "",
    ]
    for row in rows:
        lines.extend(
            [
                f"### {row['route_name']}",
                "",
                f"- Attempted bridge: {row['attempted_bridge']}",
                f"- Why it fails: {row['why_it_fails']}",
                f"- Next valid claim: {row['next_valid_claim']}",
                "",
            ]
        )

    lines.extend(["## Control Card", ""])
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

    write_json(out_dir / ROWS_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    (out_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")

    print(
        json.dumps(
            {
                "contract": summary["contract"],
                "mechanism_exhaustion_closed": summary["mechanism_exhaustion_closed"],
                "structural_gap": summary["structural_gap"],
                "missing_calculation": summary["missing_calculation"],
                "route_specific_obstruction_theorem_possible": summary[
                    "route_specific_obstruction_theorem_possible"
                ],
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
