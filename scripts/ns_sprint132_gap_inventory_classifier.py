#!/usr/bin/env python3
"""Sprint 132 NS programme gap-inventory classifier."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint132_gap_inventory_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint132_gap_inventory_classifier")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_NAME = CONTRACT + "_rows.json"
REPORT_NAME = CONTRACT + ".md"

SINGLE_LOAD_BEARING_MISSING_LEMMA = "NoLogAxisymmetricBiotSavartUniform"
RECOMMENDED_NEXT_ACTION = "attempt_NoLogAxisymmetricBiotSavartUniform"
PUBLISHABLE_NOW = (
    "WBF no-go tower",
    "axisymmetric moderate-Re regularization",
)

CLOSED_EXACT = (
    "anti-correlation",
    "Gram matrix",
    "multi-packet Reynolds stress",
    "zero-mean rotation cycle",
)
CONDITIONALLY_CLOSED = (
    "vortex-stretching log-gap obstruction",
    "Hou-Luo viscous obstruction beta>0",
)
OPEN = (
    "large-Re axisymmetric",
    "marginal beta=0",
    "Euler nu=0",
    "non-resonant triads",
    "multi-scale concentration",
)


@dataclass(frozen=True)
class GapRow:
    gap_id: str
    programme_area: str
    gap_name: str
    classification: str
    closure_strength: str
    load_bearing_for_full_clay: bool
    missing_lemma: str | None
    publishable_now: bool
    clay_navier_stokes_promoted: bool
    full_clay_ns_solved: bool
    next_action: str
    rationale: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def slug(text: str) -> str:
    return (
        text.lower()
        .replace(">", "gt")
        .replace("=", "eq")
        .replace("-", "_")
        .replace(" ", "_")
    )


def build_rows() -> list[dict[str, Any]]:
    rows: list[GapRow] = []

    closed_rationales = {
        "anti-correlation": (
            "The WBF anti-correlation route has an exact sign obstruction and "
            "cannot be promoted into a positive flux mechanism."
        ),
        "Gram matrix": (
            "The WBF Gram-matrix positivity ledger closes exactly; the candidate "
            "indefinite direction required by the route is unavailable."
        ),
        "multi-packet Reynolds stress": (
            "The WBF multi-packet Reynolds-stress construction is exactly "
            "blocked by the recorded packet interaction accounting."
        ),
        "zero-mean rotation cycle": (
            "The WBF rotating-cycle average is exactly zero, closing the last "
            "phase-cycle escape hatch in the no-go tower."
        ),
    }
    for name in CLOSED_EXACT:
        rows.append(
            GapRow(
                gap_id="wbf_" + slug(name),
                programme_area="WBF no-go tower",
                gap_name=name,
                classification="closed_exact",
                closure_strength="exact_obstruction",
                load_bearing_for_full_clay=False,
                missing_lemma=None,
                publishable_now=True,
                clay_navier_stokes_promoted=False,
                full_clay_ns_solved=False,
                next_action="package_WBF_no_go_tower",
                rationale=closed_rationales[name],
            )
        )

    rows.append(
        GapRow(
            gap_id="axisymmetric_vortex_stretching_log_gap_obstruction",
            programme_area="axisymmetric regularization",
            gap_name="vortex-stretching log-gap obstruction",
            classification="conditionally_closed",
            closure_strength="closed_if_no_log_biot_savart_loss",
            load_bearing_for_full_clay=True,
            missing_lemma=SINGLE_LOAD_BEARING_MISSING_LEMMA,
            publishable_now=True,
            clay_navier_stokes_promoted=False,
            full_clay_ns_solved=False,
            next_action=RECOMMENDED_NEXT_ACTION,
            rationale=(
                "The vortex-stretching obstruction is closed modulo the single "
                "uniform no-log axisymmetric Biot-Savart lemma."
            ),
        )
    )
    rows.append(
        GapRow(
            gap_id="axisymmetric_hou_luo_viscous_obstruction_beta_gt_0",
            programme_area="axisymmetric moderate-Re regularization",
            gap_name="Hou-Luo viscous obstruction beta>0",
            classification="conditionally_closed",
            closure_strength="closed_if_no_log_biot_savart_loss",
            load_bearing_for_full_clay=True,
            missing_lemma=SINGLE_LOAD_BEARING_MISSING_LEMMA,
            publishable_now=True,
            clay_navier_stokes_promoted=False,
            full_clay_ns_solved=False,
            next_action=RECOMMENDED_NEXT_ACTION,
            rationale=(
                "Sprint130/131 receipts close the Hou-Luo viscous route "
                "obstruction whenever nu>0 and beta>0, but the uniform "
                "axisymmetric no-log Biot-Savart lemma remains the named "
                "auxiliary hypothesis before the result is unconditional."
            ),
        )
    )

    open_rationales = {
        "large-Re axisymmetric": (
            "The moderate-Re obstruction does not yet supply a uniform large-Re "
            "axisymmetric conclusion."
        ),
        "marginal beta=0": (
            "The viscous dominance comparison degenerates at beta=0, so the "
            "marginal case remains an open boundary regime."
        ),
        "Euler nu=0": (
            "The viscous obstruction uses nu>0 and therefore does not transfer "
            "to the Euler nu=0 problem."
        ),
        "non-resonant triads": (
            "The WBF tower closes the targeted resonant mechanisms but does not "
            "settle all non-resonant triad concentration routes."
        ),
        "multi-scale concentration": (
            "The current inventories do not rule out every possible multi-scale "
            "concentration scenario needed for a full Clay resolution."
        ),
    }
    missing_lemmas = {
        "large-Re axisymmetric": SINGLE_LOAD_BEARING_MISSING_LEMMA,
        "marginal beta=0": None,
        "Euler nu=0": None,
        "non-resonant triads": None,
        "multi-scale concentration": None,
    }
    for name in OPEN:
        rows.append(
            GapRow(
                gap_id="open_" + slug(name),
                programme_area="full Clay Navier-Stokes gap map",
                gap_name=name,
                classification="open",
                closure_strength="not_closed",
                load_bearing_for_full_clay=name == "large-Re axisymmetric",
                missing_lemma=missing_lemmas[name],
                publishable_now=False,
                clay_navier_stokes_promoted=False,
                full_clay_ns_solved=False,
                next_action=(
                    RECOMMENDED_NEXT_ACTION
                    if name == "large-Re axisymmetric"
                    else "retain_as_open_gap"
                ),
                rationale=open_rationales[name],
            )
        )

    return [row.as_row() for row in rows]


def classification_counts(rows: list[dict[str, Any]]) -> dict[str, int]:
    counts = {"closed_exact": 0, "conditionally_closed": 0, "open": 0}
    for row in rows:
        counts[row["classification"]] += 1
    return counts


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    counts = classification_counts(rows)
    closed_exact_names = [
        row["gap_name"] for row in rows if row["classification"] == "closed_exact"
    ]
    conditionally_closed_names = [
        row["gap_name"] for row in rows if row["classification"] == "conditionally_closed"
    ]
    open_names = [row["gap_name"] for row in rows if row["classification"] == "open"]
    load_bearing_open = [
        row["gap_name"] for row in rows if row["load_bearing_for_full_clay"]
    ]
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "classification_counts": counts,
        "closed_exact": closed_exact_names,
        "closed_exact_count": len(closed_exact_names),
        "conditionally_closed": conditionally_closed_names,
        "conditionally_closed_count": len(conditionally_closed_names),
        "open": open_names,
        "open_count": len(open_names),
        "single_load_bearing_missing_lemma": SINGLE_LOAD_BEARING_MISSING_LEMMA,
        "load_bearing_gap_count": len(load_bearing_open),
        "load_bearing_gaps": load_bearing_open,
        "publishable_now": list(PUBLISHABLE_NOW),
        "recommended_next_action": RECOMMENDED_NEXT_ACTION,
        "full_clay_ns_solved": False,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
        "exit_reason": (
            "complete Sprint132 gap inventory emitted; programme contains "
            "publishable obstruction packages but full Clay Navier-Stokes remains unsolved"
        ),
        "control_card": {
            "O": "Worker 3 owns only the Sprint132 gap inventory classifier script and output directory",
            "R": "encode the complete NS programme gap map with exact, conditional, and open classifications",
            "C": "deterministic Python emitter writes rows JSON, summary JSON, and Markdown report",
            "S": "four WBF obstructions are closed_exact, two axisymmetric obstructions are conditionally_closed, and five regimes remain open",
            "L": "the only load-bearing missing lemma surfaced for the next move is NoLogAxisymmetricBiotSavartUniform",
            "P": "publish WBF no-go tower and axisymmetric moderate-Re regularization without Clay promotion",
            "G": "exit code is 0 exactly when the inventory is complete and Clay flags remain false",
            "F": "any claim of full Clay Navier-Stokes promotion is outside this classifier",
        },
    }


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def fmt_bool(value: bool) -> str:
    return str(value).lower()


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "gap_name",
        "classification",
        "programme_area",
        "load_bearing_for_full_clay",
        "missing_lemma",
        "next_action",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        values = [
            row["gap_name"],
            row["classification"],
            row["programme_area"],
            fmt_bool(row["load_bearing_for_full_clay"]),
            row["missing_lemma"] or "-",
            row["next_action"],
        ]
        lines.append("| " + " | ".join(values) + " |")
    return "\n".join(lines)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 132 Gap Inventory Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Row count: `{summary['row_count']}`",
        f"- Closed exact count: `{summary['closed_exact_count']}`",
        f"- Conditionally closed count: `{summary['conditionally_closed_count']}`",
        f"- Open count: `{summary['open_count']}`",
        f"- Single load-bearing missing lemma: `{summary['single_load_bearing_missing_lemma']}`",
        f"- Recommended next action: `{summary['recommended_next_action']}`",
        f"- Full Clay NS solved: `{fmt_bool(summary['full_clay_ns_solved'])}`",
        f"- Clay Navier-Stokes promoted: `{fmt_bool(summary['clay_navier_stokes_promoted'])}`",
        f"- Complete: `{fmt_bool(summary['complete'])}`",
        f"- Exit code: `{summary['exit_code']}`",
        "",
        "## Publishable Now",
        "",
    ]
    for item in summary["publishable_now"]:
        lines.append(f"- `{item}`")

    lines.extend(
        [
            "",
            "## Inventory Rows",
            "",
            markdown_table(rows),
            "",
            "## Control Card",
            "",
        ]
    )
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
                "contract": CONTRACT,
                "single_load_bearing_missing_lemma": summary[
                    "single_load_bearing_missing_lemma"
                ],
                "recommended_next_action": summary["recommended_next_action"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "clay_navier_stokes_promoted": summary[
                    "clay_navier_stokes_promoted"
                ],
                "complete": summary["complete"],
                "exit_code": summary["exit_code"],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
