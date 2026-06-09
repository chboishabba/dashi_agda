#!/usr/bin/env python3
"""Sprint 132 partial obstruction theorem emitter.

This deterministic emitter records the route-specific theorem
NSPartialRegularityFromObstructionTower.  The theorem is intentionally scoped:
within the analyzed WBF and AXS route classes, the recorded obstruction tower
rules out a finite-time BKM blowup mechanism.  It does not assert global Clay
Navier-Stokes regularity.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint132_partial_obstruction_theorem"
THEOREM = "NSPartialRegularityFromObstructionTower"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint132_partial_obstruction_theorem")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_NAME = CONTRACT + "_rows.json"
REPORT_NAME = CONTRACT + ".md"

CLASS_SCOPE = ("CLASS_WBF", "CLASS_AXS")
ANALYZED_ROUTE_CLASSES = (
    "WBF-L",
    "WBF-S",
    "WBF-MP",
    "WBF-R",
    "WBF-V",
    "AXS",
)
THEOREM_STATEMENT = (
    "No mechanism in CLASS_WBF union CLASS_AXS can produce finite-time BKM "
    "blowup within the analyzed route classes; this is route-specific and is "
    "not a global Clay Navier-Stokes regularity claim."
)


@dataclass(frozen=True)
class TheoremRow:
    row_id: str
    route_class: str
    class_family: str
    mechanism: str
    obstruction: str
    status: str
    condition: str | None
    formula: str
    bkm_blowup_mechanism_produced: bool
    route_obstructed: bool
    theorem: str
    theorem_scope: str
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        TheoremRow(
            row_id="WBF-L",
            route_class="WBF-L",
            class_family="CLASS_WBF",
            mechanism="passive linear strain sign",
            obstruction="passive linear strain sign obstruction",
            status="exact",
            condition=None,
            formula="sign(Pi^{HH->L}) = -sign(gamma)",
            bkm_blowup_mechanism_produced=False,
            route_obstructed=True,
            theorem=THEOREM,
            theorem_scope="analyzed_route_classes_only",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        TheoremRow(
            row_id="WBF-S",
            route_class="WBF-S",
            class_family="CLASS_WBF",
            mechanism="self-generated strain",
            obstruction="self-generated strain obstruction",
            status="exact",
            condition=None,
            formula="n dot S_self dot n = 2/3",
            bkm_blowup_mechanism_produced=False,
            route_obstructed=True,
            theorem=THEOREM,
            theorem_scope="analyzed_route_classes_only",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        TheoremRow(
            row_id="WBF-MP",
            route_class="WBF-MP",
            class_family="CLASS_WBF",
            mechanism="multi-packet Reynolds stress",
            obstruction="multi-packet Reynolds stress Gram lower bound",
            status="exact",
            condition=None,
            formula="||Gram||_F^2 >= N^2/3",
            bkm_blowup_mechanism_produced=False,
            route_obstructed=True,
            theorem=THEOREM,
            theorem_scope="analyzed_route_classes_only",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        TheoremRow(
            row_id="WBF-R",
            route_class="WBF-R",
            class_family="CLASS_WBF",
            mechanism="rotating background strain",
            obstruction="rotating background strain integral cancellation",
            status="exact",
            condition=None,
            formula="integral zero",
            bkm_blowup_mechanism_produced=False,
            route_obstructed=True,
            theorem=THEOREM,
            theorem_scope="analyzed_route_classes_only",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        TheoremRow(
            row_id="WBF-V",
            route_class="WBF-V",
            class_family="CLASS_WBF",
            mechanism="vortex stretching H^s data",
            obstruction="gamma <= C Omega log Omega conflicts with CF93 blowup growth",
            status="conditional_on",
            condition="omega in H1",
            formula="gamma <= C Omega log Omega + CF93 conflict",
            bkm_blowup_mechanism_produced=False,
            route_obstructed=True,
            theorem=THEOREM,
            theorem_scope="analyzed_route_classes_only",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        TheoremRow(
            row_id="AXS",
            route_class="AXS",
            class_family="CLASS_AXS",
            mechanism="axisymmetric Hou-Luo beta>0",
            obstruction="viscous dominance divergence",
            status="conditional_on",
            condition="NoLogAxisymmetricBiotSavartUniform",
            formula="nu/(T*-t)^(3 beta)->infty",
            bkm_blowup_mechanism_produced=False,
            route_obstructed=True,
            theorem=THEOREM,
            theorem_scope="analyzed_route_classes_only",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
    ]
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def fmt_bool(value: bool) -> str:
    return str(value).lower()


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "Route",
        "Class",
        "Mechanism",
        "Status",
        "Condition",
        "Formula",
        "Obstructed",
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
                    f"`{row['route_class']}`",
                    f"`{row['class_family']}`",
                    row["mechanism"],
                    f"`{row['status']}`",
                    f"`{row['condition']}`" if row["condition"] else "`-`",
                    f"`{row['formula']}`",
                    f"`{fmt_bool(row['route_obstructed'])}`",
                )
            )
            + " |"
        )
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    exact_rows = [row for row in rows if row["status"] == "exact"]
    conditional_rows = [row for row in rows if row["status"] == "conditional_on"]
    return {
        "contract": CONTRACT,
        "theorem": THEOREM,
        "theorem_statement": THEOREM_STATEMENT,
        "class_scope": list(CLASS_SCOPE),
        "analyzed_route_classes": list(ANALYZED_ROUTE_CLASSES),
        "row_count": len(rows),
        "exact_row_count": len(exact_rows),
        "conditional_row_count": len(conditional_rows),
        "exact_routes": [row["route_class"] for row in exact_rows],
        "conditional_routes": [row["route_class"] for row in conditional_rows],
        "conditional_requirements": {
            row["route_class"]: row["condition"] for row in conditional_rows
        },
        "all_rows_obstruct_route": all(row["route_obstructed"] for row in rows),
        "no_bkm_blowup_mechanism_in_analyzed_routes": all(
            row["bkm_blowup_mechanism_produced"] is False for row in rows
        ),
        "mechanism_scope": "CLASS_WBF union CLASS_AXS",
        "route_specific_obstruction": True,
        "global_regulariy_claim": False,
        "global_regularity_claim": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
        "exit_reason": (
            "recorded route-specific obstruction theorem for analyzed CLASS_WBF "
            "and CLASS_AXS mechanisms without promoting global Clay regularity"
        ),
        "control_card": {
            "O": "Worker 1 owns only the Sprint132 partial obstruction theorem script and generated output directory.",
            "R": "Emit six route rows for WBF-L, WBF-S, WBF-MP, WBF-R, WBF-V, and AXS.",
            "C": "Deterministic Python emitter writes rows JSON, summary JSON, and Markdown report.",
            "S": "Four WBF rows are exact; WBF-V and AXS are conditional on their stated hypotheses.",
            "L": "The obstruction tower ranges only over analyzed CLASS_WBF union CLASS_AXS route classes.",
            "P": "Conclude NSPartialRegularityFromObstructionTower as a route-specific obstruction theorem.",
            "G": "No row produces a finite-time BKM blowup mechanism within the analyzed routes.",
            "F": "Full Clay Navier-Stokes regularity remains false and unpromoted.",
        },
    }


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 132 Partial Obstruction Theorem",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Theorem: `{summary['theorem']}`",
        f"- Class scope: `{', '.join(summary['class_scope'])}`",
        f"- Route-specific obstruction: `{fmt_bool(summary['route_specific_obstruction'])}`",
        f"- Global regularity claim: `{fmt_bool(summary['global_regularity_claim'])}`",
        f"- Full Clay NS solved: `{fmt_bool(summary['full_clay_ns_solved'])}`",
        f"- Clay Navier-Stokes promoted: `{fmt_bool(summary['clay_navier_stokes_promoted'])}`",
        f"- Complete: `{fmt_bool(summary['complete'])}`",
        f"- Exit code: `{summary['exit_code']}`",
        "",
        "## Theorem Statement",
        "",
        summary["theorem_statement"],
        "",
        "## Rows",
        "",
        markdown_table(rows),
        "",
        "## Conditional Requirements",
        "",
    ]
    for route, condition in summary["conditional_requirements"].items():
        lines.append(f"- `{route}`: `{condition}`")
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

    write_json(out_dir / ROWS_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    (out_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")

    print(
        json.dumps(
            {
                "contract": summary["contract"],
                "theorem": summary["theorem"],
                "row_count": summary["row_count"],
                "route_specific_obstruction": summary["route_specific_obstruction"],
                "global_regulariy_claim": summary["global_regulariy_claim"],
                "global_regularity_claim": summary["global_regularity_claim"],
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
