#!/usr/bin/env python3
"""Fail-closed audit for the latest NS-A stationarity candidate.

This diagnostic records the Gaussian weighted W_r energy-ODE route for the
current A1/A3 stationarity candidate:

    alpha = 1/6, delta_r = O(r^min(1/4, alpha)).

It also records the Abel summation q choice used to test whether the candidate
rate is summable.  The output is intentionally non-promoting.  It is an audit
surface, not a PDE proof, theorem receipt, Agda validation, or Clay promotion.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import sys
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence


CONTRACT = "ns_stationarity_candidate_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_stationarity_candidate_audit")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

REQUIRED_THEOREM_IDS = (
    "A1.1",
    "A1.2",
    "A1.3",
    "A3.1",
    "A3.2",
    "A3.3",
    "A3.4",
)

ROW_FIELDS = (
    "theorem_id",
    "gate",
    "candidate_claim",
    "route_component",
    "candidate_status",
    "proved",
    "promoted",
    "blocks_promotion",
    "diagnostic_note",
)


@dataclass(frozen=True)
class CandidateRow:
    theorem_id: str
    gate: str
    candidate_claim: str
    route_component: str
    candidate_status: str
    proved: bool
    promoted: bool
    blocks_promotion: bool
    diagnostic_note: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--out-dir", type=Path, default=None)
    parser.add_argument(
        "--format",
        choices=("json", "md"),
        default="json",
        help="Output format for stdout. JSON is the default.",
    )
    parser.add_argument(
        "--pressure-tail-alpha",
        default="1/6",
        help="Candidate pressure-tail exponent alpha.",
    )
    parser.add_argument(
        "--gaussian-cutoff-rate",
        default="1/4",
        help="Gaussian weighted W_r route cutoff exponent.",
    )
    parser.add_argument(
        "--abel-q",
        type=int,
        default=7,
        help="Candidate integer q for Abel summation.",
    )
    parser.add_argument(
        "--write-default-out-dir",
        action="store_true",
        help="Write artifacts to outputs/ns_stationarity_candidate_audit.",
    )
    return parser.parse_args(argv)


def parse_fraction(raw: str, name: str) -> Fraction:
    try:
        value = Fraction(raw)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError(f"{name} must be a finite rational number") from exc
    if value <= 0:
        raise ValueError(f"{name} must be positive")
    if value >= 1:
        raise ValueError(f"{name} must be below 1 for this small-scale rate audit")
    return value


def frac_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def build_rows(beta: Fraction, alpha: Fraction, cutoff_rate: Fraction) -> list[dict[str, Any]]:
    rows = [
        CandidateRow(
            theorem_id="A1.1",
            gate="bounded Abel weighted defect mass",
            candidate_claim="sup_r ||mu_r||_TV <= C_A1(R,M) on reciprocal Gaussian/Abel windows",
            route_component="A1 mass input feeding Gaussian weighted W_r energy ODE",
            candidate_status="candidate_open_not_proved",
            proved=False,
            promoted=False,
            blocks_promotion=True,
            diagnostic_note="bounded mass remains an upstream candidate requirement",
        ),
        CandidateRow(
            theorem_id="A1.2",
            gate="weak-star compactness and tightness",
            candidate_claim="bounded Abel branch admits a tight weak-star subsequence",
            route_component="compactness branch for stationarity candidate",
            candidate_status="candidate_open_not_proved",
            proved=False,
            promoted=False,
            blocks_promotion=True,
            diagnostic_note="no PDE measure construction is promoted by this audit",
        ),
        CandidateRow(
            theorem_id="A1.3",
            gate="quantitative shell-tail control",
            candidate_claim="Gaussian/Abel shell tail is uniformly small outside reciprocal windows",
            route_component="tail budget needed before A3 summation",
            candidate_status="candidate_open_not_proved",
            proved=False,
            promoted=False,
            blocks_promotion=True,
            diagnostic_note="tail constants remain candidate data",
        ),
        CandidateRow(
            theorem_id="A3.1",
            gate="Gaussian weighted W_r energy ODE",
            candidate_claim="derive localized energy ODE for W_r = U_r - U_infinity with Gaussian weight",
            route_component="energy_ode_route",
            candidate_status="candidate_open_not_proved",
            proved=False,
            promoted=False,
            blocks_promotion=True,
            diagnostic_note="pressure, transport, cutoff, and A1 inputs remain separately budgeted",
        ),
        CandidateRow(
            theorem_id="A3.2",
            gate="pressure-tail exponent intake",
            candidate_claim=f"pressure-tail exponent alpha = {frac_text(alpha)}",
            route_component="pressure_tail_alpha_candidate",
            candidate_status="candidate_external_intake_not_proved",
            proved=False,
            promoted=False,
            blocks_promotion=True,
            diagnostic_note="alpha is recorded as candidate input only",
        ),
        CandidateRow(
            theorem_id="A3.3",
            gate="stationarity-defect rate",
            candidate_claim=(
                "delta_r = O(r^min(1/4, alpha)) = "
                f"O(r^{frac_text(beta)}) for alpha = {frac_text(alpha)}"
            ),
            route_component="delta_r_candidate_rate",
            candidate_status="candidate_open_not_proved",
            proved=False,
            promoted=False,
            blocks_promotion=True,
            diagnostic_note=(
                f"min({frac_text(cutoff_rate)}, {frac_text(alpha)}) = {frac_text(beta)}; "
                "the estimate is not certified by this diagnostic"
            ),
        ),
        CandidateRow(
            theorem_id="A3.4",
            gate="Abel summation q choice",
            candidate_claim="choose integer q with q * min(1/4, alpha) > 1",
            route_component="abel_summation_q_candidate",
            candidate_status="candidate_passes_numeric_q_check_not_proved",
            proved=False,
            promoted=False,
            blocks_promotion=True,
            diagnostic_note="numeric q margin is necessary bookkeeping, not an Abel closure proof",
        ),
    ]
    return [row.as_row() for row in rows]


def build_summary(args: argparse.Namespace) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    repo_root = args.repo_root.resolve()
    alpha = parse_fraction(args.pressure_tail_alpha, "pressure-tail alpha")
    cutoff_rate = parse_fraction(args.gaussian_cutoff_rate, "gaussian cutoff rate")
    beta = min(cutoff_rate, alpha)
    if args.abel_q <= 0:
        raise ValueError("--abel-q must be positive")
    abel_q_beta = Fraction(args.abel_q) * beta
    q_threshold = math.floor(1.0 / float(beta)) + 1
    rows = build_rows(beta=beta, alpha=alpha, cutoff_rate=cutoff_rate)
    theorem_ids = [row["theorem_id"] for row in rows]

    promotion_status = {
        "candidate_only": True,
        "proved": False,
        "stationarity_proved": False,
        "pde_measure_constructed": False,
        "abel_summation_closed": False,
        "promoted": False,
        "promotion_allowed": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "full_clay_ns_solved": False,
    }
    checks = {
        "required_theorem_ids_present": set(REQUIRED_THEOREM_IDS) <= set(theorem_ids),
        "required_theorem_ids_exact": tuple(theorem_ids) == REQUIRED_THEOREM_IDS,
        "alpha_is_one_sixth": alpha == Fraction(1, 6),
        "beta_matches_min_cutoff_and_alpha": beta == min(cutoff_rate, alpha),
        "candidate_delta_exponent_positive": beta > 0,
        "abel_q_beta_greater_than_one": abel_q_beta > 1,
        "no_row_proved_or_promoted": all(
            row["proved"] is False and row["promoted"] is False for row in rows
        ),
        "promotion_flags_fail_closed": all(value is False for value in promotion_status.values() if value is not True),
    }
    checks["valid"] = all(checks.values())

    summary = {
        "contract": CONTRACT,
        "repo_root": str(repo_root),
        "candidate_name": "NS-A stationarity candidate: Gaussian weighted W_r energy-ODE route",
        "route": "gaussian_weighted_W_r_energy_ODE",
        "status": "candidate_non_promoting_fail_closed",
        "candidate_status": "candidate_only_non_promoting",
        "theorem_id_range": "A1.1-A3.4",
        "required_theorem_ids": list(REQUIRED_THEOREM_IDS),
        "present_theorem_ids": theorem_ids,
        "pressure_tail_alpha": {
            "raw": args.pressure_tail_alpha,
            "fraction": frac_text(alpha),
            "value": float(alpha),
        },
        "gaussian_cutoff_rate": {
            "raw": args.gaussian_cutoff_rate,
            "fraction": frac_text(cutoff_rate),
            "value": float(cutoff_rate),
        },
        "delta_r_candidate": {
            "formula": "O(r^min(1/4, alpha))",
            "min_exponent_fraction": frac_text(beta),
            "min_exponent_value": float(beta),
            "for_alpha_one_sixth": "O(r^1/6)",
            "proved": False,
            "promoted": False,
        },
        "abel_summation": {
            "q": args.abel_q,
            "q_threshold_strict": q_threshold,
            "criterion": "q * min(1/4, alpha) > 1",
            "q_times_beta_fraction": frac_text(abel_q_beta),
            "q_times_beta_value": float(abel_q_beta),
            "numeric_margin_fraction": frac_text(abel_q_beta - 1),
            "numeric_check_passes": abel_q_beta > 1,
            "closure_proved": False,
            "promoted": False,
        },
        "promotion_status": promotion_status,
        "checks": checks,
        "row_count": len(rows),
        "exit_code": 0 if checks["valid"] else 2,
        "exit_reason": (
            "candidate audit complete; all fail-closed invariants held"
            if checks["valid"]
            else "candidate audit failed one or more fail-closed invariants"
        ),
        "control_card": {
            "O": "Worker 1 owns scripts/ns_stationarity_candidate_audit.py and tests/test_ns_stationarity_candidate_audit.py only.",
            "R": "Record the latest NS-A stationarity candidate with A1.1-A3.4 IDs, Gaussian W_r ODE route, alpha=1/6, delta_r exponent min(1/4,alpha), Abel q choice, and non-promotion statuses.",
            "C": "Pure stdlib audit with JSON default, optional Markdown, and optional JSON/CSV/Markdown artifacts.",
            "S": "Candidate bookkeeping only: no PDE measure construction, no proved stationarity, no Abel closure theorem, no Clay promotion.",
            "L": "A1.1 mass -> A1.2 tightness -> A1.3 shell tail -> A3.1 W_r ODE -> A3.2 alpha -> A3.3 delta_r -> A3.4 Abel q.",
            "P": "Use q * beta > 1 as a numeric diagnostic gate while keeping all theorem and promotion gates fail-closed.",
            "G": "The audit must fail if any required theorem ID is missing or any proved/promoted flag becomes true.",
            "F": "Remaining work is the actual analytic proof package and independent promotion receipt; this diagnostic cannot promote it.",
        },
    }
    return summary, rows


def validate_payload(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    errors: list[str] = []
    if tuple(summary["present_theorem_ids"]) != REQUIRED_THEOREM_IDS:
        errors.append("present theorem IDs do not exactly match required A1.1-A3.4 IDs")
    for row in rows:
        if row.get("proved") is not False:
            errors.append(f"{row.get('theorem_id')} row proved flag is not false")
        if row.get("promoted") is not False:
            errors.append(f"{row.get('theorem_id')} row promoted flag is not false")
    promotion_status = summary["promotion_status"]
    for key in (
        "proved",
        "stationarity_proved",
        "pde_measure_constructed",
        "abel_summation_closed",
        "promoted",
        "promotion_allowed",
        "clay_promoted",
        "clay_navier_stokes_promoted",
        "full_clay_ns_solved",
    ):
        if promotion_status.get(key) is not False:
            errors.append(f"promotion_status.{key} must be false")
    if summary["status"] != "candidate_non_promoting_fail_closed":
        errors.append("summary status must remain candidate_non_promoting_fail_closed")
    if summary["checks"]["valid"] is not True:
        errors.append("summary checks are not valid")
    if errors:
        raise AssertionError("; ".join(errors))


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=ROW_FIELDS)
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Stationarity Candidate Audit",
        "",
        f"- Status: `{summary['status']}`",
        f"- Route: `{summary['route']}`",
        f"- Pressure-tail alpha: `{summary['pressure_tail_alpha']['fraction']}`",
        f"- Candidate delta_r: `{summary['delta_r_candidate']['formula']}` = `{summary['delta_r_candidate']['for_alpha_one_sixth']}`",
        f"- Abel q: `{summary['abel_summation']['q']}` with q beta `{summary['abel_summation']['q_times_beta_fraction']}`",
        f"- Proved: `{str(summary['promotion_status']['proved']).lower()}`",
        f"- Promoted: `{str(summary['promotion_status']['promoted']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['promotion_status']['clay_navier_stokes_promoted']).lower()}`",
        "",
        "## Theorem Rows",
        "",
        "| ID | Gate | Component | Status | Proved | Promoted |",
        "| --- | --- | --- | --- | ---: | ---: |",
    ]
    for row in rows:
        lines.append(
            "| {theorem_id} | {gate} | {route_component} | {candidate_status} | {proved} | {promoted} |".format(
                **row
            )
        )
    lines.extend(
        [
            "",
            "This audit is candidate-only and fail-closed.  It records a numeric",
            "summability check but does not prove A3.4 or promote any Navier-Stokes claim.",
        ]
    )
    return "\n".join(lines) + "\n"


def maybe_write_artifacts(args: argparse.Namespace, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    out_dir = args.out_dir
    if out_dir is None and args.write_default_out_dir:
        out_dir = OUT_DIR_DEFAULT
    if out_dir is None:
        return
    repo_root = args.repo_root.resolve()
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_csv(out_dir / ROWS_CSV_NAME, rows)
    (out_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    try:
        args = parse_args(argv)
        summary, rows = build_summary(args)
        validate_payload(summary, rows)
        maybe_write_artifacts(args, summary, rows)
        if args.format == "md":
            print(render_markdown(summary, rows), end="")
        else:
            print(json.dumps(summary, indent=2, sort_keys=True))
        return int(summary["exit_code"])
    except Exception as exc:
        error_payload = {
            "contract": CONTRACT,
            "status": "audit_failed_fail_closed",
            "proved": False,
            "promoted": False,
            "clay_navier_stokes_promoted": False,
            "error": str(exc),
            "exit_code": 2,
        }
        print(json.dumps(error_payload, indent=2, sort_keys=True), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
