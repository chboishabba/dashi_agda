#!/usr/bin/env python3
"""Sprint 90 NS epsilon-budget scalar absorption solver.

Audits the scalar condition

    C * (K*)^(-1/2) * H1Tail <= epsilon * nu

against candidate K laws and H1-tail laws.  The solver is intentionally
fail-closed: numerical or asymptotic smallness is not enough unless an allowed
candidate supplies both a pointwise H1 tail and an epsilon-independent
coefficient source.
"""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any


getcontext().prec = 50

CONTRACT = "ns_sprint90_epsilon_budget_solver"
ROUTE_FAIL_CLOSED = "fail-closed"
REQUIRED_RESIDUAL_GATE = "PointwiseH1TailWithIndependentEpsilonCoefficient"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint90_epsilon_budget_solver")
SUMMARY_NAME = "ns_sprint90_epsilon_budget_solver_summary.json"
CANDIDATE_TABLE = "ns_sprint90_epsilon_budget_solver_candidate_table.csv"
GATE_TABLE = "ns_sprint90_epsilon_budget_solver_gate_table.csv"
REPORT_NAME = "ns_sprint90_epsilon_budget_solver_report.md"


@dataclass(frozen=True)
class KLaw:
    law_id: str
    name: str
    exponent_alpha: Fraction
    expression: str


@dataclass(frozen=True)
class TailLaw:
    law_id: str
    name: str
    exponent_beta: Fraction
    coefficient: Decimal
    expression: str
    pointwise_h1_tail: bool
    independent_epsilon_coefficient: bool
    allowed_candidate: bool
    supplied: bool
    status: str
    blocker: str


K_LAWS = [
    KLaw("K1", "nu^-1", Fraction(1, 1), "K* = nu^-1"),
    KLaw("K2", "nu^-4/3", Fraction(4, 3), "K* = nu^-4/3"),
    KLaw("K3", "nu^-2", Fraction(2, 1), "K* = nu^-2"),
]

TAIL_LAWS = [
    TailLaw(
        "T1",
        "Leray-only",
        Fraction(0, 1),
        Decimal("1"),
        "H1Tail <= C_L",
        False,
        False,
        False,
        True,
        "REJECTED",
        "Leray energy does not give pointwise danger-shell H1-tail smallness.",
    ),
    TailLaw(
        "T2",
        "time-integrated-only",
        Fraction(1, 1),
        Decimal("1"),
        "integral H1Tail dt <= C_T * nu",
        False,
        False,
        False,
        True,
        "REJECTED",
        "Time-integrated dissipation is not a pointwise-in-time H1-tail bound.",
    ),
    TailLaw(
        "T3",
        "local-enstrophy-candidate",
        Fraction(1, 1),
        Decimal("0.5"),
        "H1Tail <= c_LE * nu on danger shell",
        True,
        False,
        True,
        True,
        "REJECTED",
        "Candidate is pointwise but lacks an epsilon-independent coefficient certificate.",
    ),
    TailLaw(
        "T4",
        "required-independent-coefficient-law",
        Fraction(1, 1),
        Decimal("0.01"),
        "H1Tail <= c_ind * nu with c_ind independent of target epsilon",
        True,
        True,
        False,
        False,
        "NOT_SUPPLIED",
        "This is the required law shape, but no supplied receipt/candidate provides it.",
    ),
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--C", dest="constant_c", type=Decimal, default=Decimal("1"))
    parser.add_argument("--epsilon", type=Decimal, default=Decimal("0.1"))
    parser.add_argument(
        "--nu-grid",
        type=Decimal,
        nargs="*",
        default=[Decimal("1"), Decimal("0.1"), Decimal("0.01"), Decimal("0.001")],
    )
    return parser.parse_args()


def decimal_power_nu(nu: Decimal, exponent: Fraction) -> Decimal:
    if exponent.denominator == 1:
        return nu ** exponent.numerator
    return Decimal(str(float(nu) ** float(exponent)))


def format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def evaluate_candidate(k_law: KLaw, tail_law: TailLaw, constant_c: Decimal, epsilon: Decimal, nu_grid: list[Decimal]) -> dict[str, Any]:
    lhs_exponent = tail_law.exponent_beta + k_law.exponent_alpha / 2
    ratio_exponent = lhs_exponent - 1
    ratios = []
    for nu in nu_grid:
        ratio = (constant_c * tail_law.coefficient / epsilon) * decimal_power_nu(nu, ratio_exponent)
        ratios.append(ratio)

    numeric_absorbed_on_grid = all(ratio <= Decimal("1") for ratio in ratios)
    asymptotically_nonworse = ratio_exponent >= 0
    supplies_required_evidence = (
        tail_law.allowed_candidate
        and tail_law.supplied
        and tail_law.pointwise_h1_tail
        and tail_law.independent_epsilon_coefficient
    )
    accepted = numeric_absorbed_on_grid and asymptotically_nonworse and supplies_required_evidence

    if accepted:
        status = "ACCEPTED"
    elif not supplies_required_evidence:
        status = "FAIL_CLOSED_EVIDENCE_MISSING"
    elif not asymptotically_nonworse:
        status = "FAIL_CLOSED_ASYMPTOTIC_EXPONENT"
    else:
        status = "FAIL_CLOSED_NUMERIC_GRID"

    return {
        "k_law_id": k_law.law_id,
        "k_law": k_law.name,
        "k_expression": k_law.expression,
        "k_exponent_alpha": format_fraction(k_law.exponent_alpha),
        "tail_law_id": tail_law.law_id,
        "tail_law": tail_law.name,
        "tail_expression": tail_law.expression,
        "tail_exponent_beta": format_fraction(tail_law.exponent_beta),
        "tail_coefficient": str(tail_law.coefficient),
        "lhs_nu_exponent_beta_plus_alpha_over_2": format_fraction(lhs_exponent),
        "ratio_nu_exponent": format_fraction(ratio_exponent),
        "asymptotically_nonworse_than_epsilon_nu": asymptotically_nonworse,
        "numeric_absorbed_on_grid": numeric_absorbed_on_grid,
        "max_grid_ratio": str(max(ratios)),
        "grid_ratios": "; ".join(f"nu={nu}:ratio={ratio}" for nu, ratio in zip(nu_grid, ratios)),
        "pointwise_h1_tail": tail_law.pointwise_h1_tail,
        "independent_epsilon_coefficient": tail_law.independent_epsilon_coefficient,
        "allowed_candidate": tail_law.allowed_candidate,
        "supplied": tail_law.supplied,
        "supplies_required_evidence": supplies_required_evidence,
        "accepted": accepted,
        "status": status,
        "blocker": tail_law.blocker,
    }


def gate_rows(candidate_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    any_allowed_supplied = any(row["allowed_candidate"] and row["supplied"] for row in candidate_rows)
    any_pointwise = any(row["allowed_candidate"] and row["supplied"] and row["pointwise_h1_tail"] for row in candidate_rows)
    any_independent = any(
        row["allowed_candidate"] and row["supplied"] and row["independent_epsilon_coefficient"] for row in candidate_rows
    )
    any_evidence_complete = any(row["supplies_required_evidence"] for row in candidate_rows)
    any_accepted = any(row["accepted"] for row in candidate_rows)
    return [
        {
            "gate_id": "G1",
            "gate_name": "AllowedCandidateSupplied",
            "passed": any_allowed_supplied,
            "status": "PASS" if any_allowed_supplied else "FAIL_CLOSED",
            "next_required_input": "Supply an allowed candidate law rather than an inadmissible energy/time-integrated proxy.",
        },
        {
            "gate_id": "G2",
            "gate_name": "PointwiseH1TailSupplied",
            "passed": any_pointwise,
            "status": "PASS" if any_pointwise else "FAIL_CLOSED",
            "next_required_input": "Supply a pointwise-in-time danger-shell H1-tail estimate.",
        },
        {
            "gate_id": "G3",
            "gate_name": "IndependentEpsilonCoefficientSupplied",
            "passed": any_independent,
            "status": "PASS" if any_independent else "FAIL_CLOSED",
            "next_required_input": "Supply a coefficient source independent of the target absorption epsilon.",
        },
        {
            "gate_id": "G4",
            "gate_name": "EvidenceComplete",
            "passed": any_evidence_complete,
            "status": "PASS" if any_evidence_complete else "FAIL_CLOSED",
            "next_required_input": "Provide both pointwise H1 tail and independent epsilon coefficient in one allowed supplied candidate.",
        },
        {
            "gate_id": "G5",
            "gate_name": "ScalarAbsorptionAccepted",
            "passed": any_accepted,
            "status": "PASS" if any_accepted else "FAIL_CLOSED",
            "next_required_input": "Re-run after an allowed evidence-complete candidate is supplied.",
        },
    ]


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def build(constant_c: Decimal, epsilon: Decimal, nu_grid: list[Decimal]) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]:
    candidates = [
        evaluate_candidate(k_law, tail_law, constant_c, epsilon, nu_grid)
        for k_law in K_LAWS
        for tail_law in TAIL_LAWS
    ]
    gates = gate_rows(candidates)
    accepted = [row for row in candidates if row["accepted"]]
    evidence_complete = [row for row in candidates if row["supplies_required_evidence"]]
    summary = {
        "contract": CONTRACT,
        "route": ROUTE_FAIL_CLOSED if not accepted else "accepted",
        "route_decision": ROUTE_FAIL_CLOSED if not accepted else "accepted",
        "final_decision": "FAIL_CLOSED" if not accepted else "ACCEPTED",
        "required_residual_gate": REQUIRED_RESIDUAL_GATE,
        "condition": "C*(K*)^-1/2*H1Tail <= epsilon*nu",
        "constant_C": str(constant_c),
        "epsilon": str(epsilon),
        "nu_grid": [str(nu) for nu in nu_grid],
        "candidate_count": len(candidates),
        "accepted_candidate_count": len(accepted),
        "evidence_complete_candidate_count": len(evidence_complete),
        "fail_closed_reason": (
            "No allowed supplied candidate provides both pointwise H1 tail and an epsilon-independent coefficient."
            if not evidence_complete
            else "Evidence exists, but scalar/asymptotic absorption failed."
        ),
        "k_laws": [asdict(k_law) | {"exponent_alpha": format_fraction(k_law.exponent_alpha)} for k_law in K_LAWS],
        "tail_laws": [
            asdict(tail_law) | {"exponent_beta": format_fraction(tail_law.exponent_beta), "coefficient": str(tail_law.coefficient)}
            for tail_law in TAIL_LAWS
        ],
    }
    return summary, candidates, gates


def write_report(path: Path, summary: dict[str, Any], candidates: list[dict[str, Any]], gates: list[dict[str, Any]]) -> None:
    accepted = [row for row in candidates if row["accepted"]]
    lines = [
        "# NS Sprint 90 Epsilon Budget Solver",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Decision: `{summary['final_decision']}`",
        f"- Condition: `{summary['condition']}`",
        f"- C: `{summary['constant_C']}`",
        f"- epsilon: `{summary['epsilon']}`",
        f"- Candidate pairs evaluated: `{summary['candidate_count']}`",
        f"- Accepted candidate pairs: `{summary['accepted_candidate_count']}`",
        "",
        "## Gate Results",
        "",
    ]
    for gate in gates:
        lines.append(f"- {gate['gate_id']} {gate['gate_name']}: `{gate['status']}`")
    lines.extend(
        [
            "",
            "## Conclusion",
            "",
            "The audit fails closed. Leray-only and time-integrated-only tails are not pointwise H1-tail estimates. "
            "The local-enstrophy candidate is pointwise but lacks an independent epsilon coefficient. "
            "The required independent-coefficient law is listed as the necessary law shape, but it is not supplied.",
            "",
            "No Clay Navier-Stokes promotion or scalar absorption closure is certified by this calculator.",
        ]
    )
    if accepted:
        lines.extend(["", "## Accepted Candidates", ""])
        for row in accepted:
            lines.append(f"- {row['k_law']} with {row['tail_law']}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary, candidates, gates = build(args.constant_c, args.epsilon, args.nu_grid)
    (args.out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_csv(args.out_dir / CANDIDATE_TABLE, candidates)
    write_csv(args.out_dir / GATE_TABLE, gates)
    write_report(args.out_dir / REPORT_NAME, summary, candidates, gates)
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
