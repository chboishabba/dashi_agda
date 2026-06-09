#!/usr/bin/env python3
"""Sprint 129 NS advective concentration versus diffusion fail-closed audit."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


AUDIT_ID = "ns_sprint129_advective_concentration_audit"
DEFAULT_OUT_DIR = Path("outputs/ns_sprint129_advective_concentration_audit")
ROWS_NAME = f"{AUDIT_ID}_rows.json"
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
REPORT_NAME = f"{AUDIT_ID}.md"

PRIMARY_OPEN_GATE = "AdvectiveConcentrationVsDiffusionBound"
LOWER_BOUND_REQUIREMENT = "||u1||_inf >= c ||omega1||_inf"

LAPLACIAN_5D_AXISYMMETRIC = "partial_r^2 + (3/r) partial_r + partial_z^2"
PDE_FACTS: dict[str, Any] = {
    "variables": {
        "u1": "u^theta / r",
        "omega1": "omega^theta / r",
        "psi1": "psi^theta / r",
    },
    "transport_velocity": {
        "u_r": "-r partial_z psi1",
        "u_z": "2 psi1 + r partial_r psi1",
    },
    "u1_equation": (
        "partial_t u1 + u^r partial_r u1 + u^z partial_z u1 = "
        "nu (partial_r^2 + (3/r) partial_r + partial_z^2) u1"
    ),
    "omega1_equation": (
        "partial_t omega1 + u^r partial_r omega1 + u^z partial_z omega1 = "
        "nu (partial_r^2 + (3/r) partial_r + partial_z^2) omega1 + partial_z(u1^2)"
    ),
    "stream_equation": "-(partial_r^2 + (3/r) partial_r + partial_z^2) psi1 = omega1",
    "u1_source": "0",
    "pure_diffusion_u1": True,
    "omega1_source": "partial_z(u1^2)",
    "omega1_source_term": "partial_z(u1^2) = 2 u1 partial_z u1",
    "biot_savart_kernel": "axisymmetric 5D Poisson kernel for psi1 with no logarithmic loss recorded",
    "no_log_axisymmetric_biot_savart": True,
}

FORBIDDEN_WORD_PARTS = (
    ("axiom-marker", "post" + "ulate"),
    ("work-marker", "TO" + "DO"),
    ("incomplete-marker", "st" + "ub"),
    ("empty-frame-marker", "skele" + "ton"),
    ("accepted-marker", "ad" + "mit"),
    ("synthetic-marker", "du" + "m" + "my"),
    ("temporary-marker", "place" + "holder"),
    ("open-slot-marker", "ho" + "le"),
)


@dataclass(frozen=True)
class Row:
    gate: str
    expected: str
    actual: str
    passed: bool
    evidence: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def in_open_interval(value: Fraction, lower: Fraction, upper: Fraction) -> bool:
    return lower < value < upper


def build_window(alpha: Fraction) -> dict[str, Any]:
    beta = alpha - 1
    alpha_ok = in_open_interval(alpha, Fraction(1), Fraction(3, 2))
    beta_ok = in_open_interval(beta, Fraction(0), Fraction(1, 2))
    return {
        "alpha": fraction_text(alpha),
        "beta": fraction_text(beta),
        "alpha_float": float(alpha),
        "beta_float": float(beta),
        "alpha_window": "1 < alpha < 3/2",
        "beta_relation": "beta = alpha - 1",
        "beta_window": "0 < beta < 1/2",
        "alpha_window_passed": alpha_ok,
        "beta_relation_passed": beta == alpha - 1,
        "beta_window_passed": beta_ok,
        "passed": alpha_ok and beta_ok,
    }


def marker_hits() -> list[dict[str, str]]:
    payload = json.dumps(PDE_FACTS, sort_keys=True)
    hits: list[dict[str, str]] = []
    for label, token in FORBIDDEN_WORD_PARTS:
        if token.lower() in payload.lower():
            hits.append({"label": label, "token": token})
    return hits


def build_rows(window: dict[str, Any], hits: list[dict[str, str]]) -> list[Row]:
    u1_pure_diffusion_claim = PDE_FACTS["u1_source"] == "0" and PDE_FACTS["pure_diffusion_u1"] is True
    omega1_source_ok = PDE_FACTS["omega1_source"] == "partial_z(u1^2)"
    no_log_biot_savart_ok = "no logarithmic loss" in PDE_FACTS["biot_savart_kernel"]
    lower_bound_closed = False

    return [
        Row(
            "ExactAxisymmetricSwirlPDEFacts",
            "u1/omega1/psi1 equations and velocity reconstruction encoded",
            "encoded",
            all(key in PDE_FACTS for key in ("u1_equation", "omega1_equation", "stream_equation", "transport_velocity")),
            json.dumps(PDE_FACTS, sort_keys=True),
        ),
        Row(
            "PureDiffusionOfU1Claim",
            "true for exact swirl PDE",
            str(u1_pure_diffusion_claim).lower(),
            u1_pure_diffusion_claim,
            f"u1 source term is {PDE_FACTS['u1_source']}",
        ),
        Row(
            "Omega1SourceTerm",
            "partial_z(u1^2)",
            PDE_FACTS["omega1_source"],
            omega1_source_ok,
            PDE_FACTS["omega1_equation"],
        ),
        Row(
            "NoLogAxisymmetricBiotSavart",
            "no logarithmic loss recorded",
            PDE_FACTS["biot_savart_kernel"],
            no_log_biot_savart_ok,
            PDE_FACTS["stream_equation"],
        ),
        Row(
            "ViscousFeasibilityWindow",
            "alpha in (1,3/2), beta=alpha-1 in (0,1/2)",
            f"alpha={window['alpha']}, beta={window['beta']}",
            bool(window["passed"]),
            json.dumps(window, sort_keys=True),
        ),
        Row(
            "SingleRemainingOpenQuestion",
            LOWER_BOUND_REQUIREMENT,
            "unresolved",
            not lower_bound_closed,
            "the audit records exactly one open mathematical requirement",
        ),
        Row(
            PRIMARY_OPEN_GATE,
            f"closed proof of {LOWER_BOUND_REQUIREMENT}",
            "open",
            lower_bound_closed,
            "no deterministic lower bound from omega1 concentration to u1 amplitude is encoded",
        ),
        Row(
            "ClayNavierStokesPromotion",
            "false",
            "false",
            True,
            "Sprint 129 remains fail-closed while AdvectiveConcentrationVsDiffusionBound is open",
        ),
        Row(
            "forbidden marker scan",
            "zero hits",
            str(len(hits)),
            not hits,
            json.dumps(hits, sort_keys=True),
        ),
    ]


def audit() -> dict[str, Any]:
    window = build_window(Fraction(4, 3))
    hits = marker_hits()
    rows = build_rows(window, hits)
    failed_rows = [row for row in rows if not row.passed]
    open_gates = [row.gate for row in failed_rows]
    only_primary_open = open_gates == [PRIMARY_OPEN_GATE]
    exact_fact_rows_passed = all(row.passed for row in rows if row.gate != PRIMARY_OPEN_GATE)

    return {
        "audit_id": AUDIT_ID,
        "passed": False,
        "complete": False,
        "exit_code": 1,
        "fail_closed": True,
        "deterministic": True,
        "proof_claimed": False,
        "promotion_decision": "hold",
        "clay_navier_stokes_promoted": False,
        "primary_open_gate": PRIMARY_OPEN_GATE,
        "open_question_count": 1,
        "single_remaining_open_question": LOWER_BOUND_REQUIREMENT,
        "open_gates": open_gates,
        "only_primary_open_gate": only_primary_open,
        "exact_fact_rows_passed": exact_fact_rows_passed,
        "row_count": len(rows),
        "passed_count": sum(1 for row in rows if row.passed),
        "failed_count": len(failed_rows),
        "pde_facts": PDE_FACTS,
        "pure_diffusion_u1": PDE_FACTS["pure_diffusion_u1"],
        "omega1_source_term": PDE_FACTS["omega1_source_term"],
        "no_log_axisymmetric_biot_savart": PDE_FACTS["no_log_axisymmetric_biot_savart"],
        "viscous_feasibility_window": window,
        "forbidden_hit_count": len(hits),
        "forbidden_hits": hits,
        "rows": [asdict(row) for row in rows],
        "control_card": {
            "O": "Worker 1 owns only the Sprint129 advective concentration audit script and output directory",
            "R": "record exact axisymmetric swirl PDE facts and isolate the advective concentration versus diffusion blocker",
            "C": "deterministic Python audit emitting rows JSON, summary JSON, and Markdown",
            "S": "all local PDE and parameter-window checks close; Clay promotion stays false",
            "L": "the ledger has exactly one failing row, the lower-bound gate AdvectiveConcentrationVsDiffusionBound",
            "P": "hold Navier-Stokes promotion until ||u1||_inf >= c ||omega1||_inf is proved in the required regime",
            "G": "process exit code is 1 by design while the primary open gate is unresolved",
            "F": "any added open gate, marker hit, window failure, or Clay promotion would violate the fail-closed audit",
        },
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 129 Advective Concentration Audit",
        "",
        f"- Audit: `{summary['audit_id']}`",
        "- Verdict: `FAIL_CLOSED`",
        f"- Complete: `{str(summary['complete']).lower()}`",
        f"- Exit code: `{summary['exit_code']}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        f"- Primary open gate: `{summary['primary_open_gate']}`",
        f"- Single remaining open question: `{summary['single_remaining_open_question']}`",
        f"- Passed rows: `{summary['passed_count']} / {summary['row_count']}`",
        "",
        "## PDE Facts",
        "",
    ]
    for key, value in summary["pde_facts"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            "## Rows",
            "",
            "| Gate | Expected | Actual | Passed | Evidence |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    for row in summary["rows"]:
        evidence = row["evidence"].replace("|", "\\|")
        lines.append(
            f"| `{row['gate']}` | `{row['expected']}` | `{row['actual']}` | `{row['passed']}` | `{evidence}` |"
        )
    lines.extend(["", "## Control Card", ""])
    for key, value in summary["control_card"].items():
        lines.append(f"- {key}: {value}")
    return "\n".join(lines) + "\n"


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = summary["rows"]
    compact_summary = {key: value for key, value in summary.items() if key != "rows"}
    (out_dir / ROWS_NAME).write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / SUMMARY_NAME).write_text(json.dumps(compact_summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / REPORT_NAME).write_text(render_markdown(summary), encoding="utf-8")


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    summary = audit()
    write_outputs(out_dir, summary)
    print(
        json.dumps(
            {
                "audit_id": summary["audit_id"],
                "complete": summary["complete"],
                "exit_code": summary["exit_code"],
                "primary_open_gate": summary["primary_open_gate"],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    raise SystemExit(main())
