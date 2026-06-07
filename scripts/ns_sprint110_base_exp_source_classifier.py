#!/usr/bin/env python3
"""Sprint 110 NS base exponential source classifier."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint110_base_exp_source_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint110_base_exp_source_classifier")
SUMMARY_NAME = "ns_sprint110_base_exp_source_classifier_summary.json"
ROWS_NAME = "ns_sprint110_base_exp_source_classifier_rows.json"
CSV_NAME = "ns_sprint110_base_exp_source_classifier_rows.csv"
REPORT_NAME = "ns_sprint110_base_exp_source_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_BASE_EXP_SOURCE"

REQUIRED_GATES = (
    "exp_negative_inverse_seed",
    "smoothness_on_positive_domain",
    "derivative_hierarchy",
    "positive_interior_nonzero",
    "non_circular_source",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "imposed_derivative_hierarchy",
    "imposed_positive_interior",
    "imported_bump_package",
    "external_forcing",
    "target_kstar_collapse",
    "non_leray_regularization",
)


@dataclass(frozen=True)
class BaseExpCandidate:
    family_id: str
    family: str
    ansatz: str
    classification: str
    exp_negative_inverse_seed: bool
    smoothness_on_positive_domain: bool
    derivative_hierarchy: bool
    positive_interior_nonzero: bool
    non_circular_source: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    note: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "exp_negative_inverse_seed": self.exp_negative_inverse_seed,
            "smoothness_on_positive_domain": self.smoothness_on_positive_domain,
            "derivative_hierarchy": self.derivative_hierarchy,
            "positive_interior_nonzero": self.positive_interior_nonzero,
            "non_circular_source": self.non_circular_source,
            "no_forbidden_dependency": self.no_forbidden_dependency,
        }

    @property
    def accepted(self) -> bool:
        return all(self.gate_results.values())

    def row(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["forbidden_dependencies"] = (
            "none" if not self.forbidden_dependencies else ";".join(self.forbidden_dependencies)
        )
        payload["no_forbidden_dependency"] = self.no_forbidden_dependency
        payload["gate_results"] = self.gate_results
        payload["failed_gates"] = [
            gate for gate, passed in self.gate_results.items() if not passed
        ]
        payload["accepted"] = self.accepted
        return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def candidate_families() -> list[BaseExpCandidate]:
    return [
        BaseExpCandidate(
            family_id="CEN",
            family="classical_exp_negative_inverse_seed",
            ansatz="use exp(-1/x) on the positive domain as the base exponential seed",
            classification="classical smooth positive-domain seed without a derived Navier-Stokes source role",
            exp_negative_inverse_seed=True,
            smoothness_on_positive_domain=True,
            derivative_hierarchy=False,
            positive_interior_nonzero=True,
            non_circular_source=False,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "The seed is smooth and positive on x > 0, but the full derivative "
                "hierarchy needed by the closure ledger is not derived, and no "
                "non-circular Navier-Stokes source is produced."
            ),
        ),
        BaseExpCandidate(
            family_id="RPE",
            family="reciprocal_power_exp_seed",
            ansatz="replace the base exponent with exp(-1/x^p) for a selected p > 0",
            classification="parametric reciprocal-power variant with unproven hierarchy transfer",
            exp_negative_inverse_seed=False,
            smoothness_on_positive_domain=True,
            derivative_hierarchy=False,
            positive_interior_nonzero=True,
            non_circular_source=False,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "The reciprocal-power variant is smooth on the positive domain, but it "
                "is not the required exp(-1/x) seed and does not derive the hierarchy "
                "or a non-circular source."
            ),
        ),
        BaseExpCandidate(
            family_id="PDD",
            family="patched_exp_seed_with_declared_derivatives",
            ansatz="patch the base exponential seed and declare the required derivatives as available",
            classification="patched source with hierarchy supplied by declaration",
            exp_negative_inverse_seed=True,
            smoothness_on_positive_domain=False,
            derivative_hierarchy=True,
            positive_interior_nonzero=True,
            non_circular_source=False,
            forbidden_dependencies=("imposed_derivative_hierarchy",),
            verdict="reject",
            note=(
                "The derivative ledger is declared rather than derived, the patching "
                "does not prove smoothness across the positive-domain construction, "
                "and the source role remains circular."
            ),
        ),
        BaseExpCandidate(
            family_id="ISB",
            family="imported_smooth_bump_seed",
            ansatz="import a smooth bump package and use its exponential-looking witness",
            classification="external bump witness with imported analytic obligations",
            exp_negative_inverse_seed=False,
            smoothness_on_positive_domain=True,
            derivative_hierarchy=True,
            positive_interior_nonzero=True,
            non_circular_source=False,
            forbidden_dependencies=("imported_bump_package", "desired_conclusion"),
            verdict="reject",
            note=(
                "The smooth bump behavior is imported from an external package and "
                "specialized toward the desired conclusion, so it does not supply an "
                "internal non-circular base exponential source."
            ),
        ),
        BaseExpCandidate(
            family_id="IBS",
            family="imposed_base_exp_smooth_function",
            ansatz="assume the base exponential smooth function, interior positivity, and source witness",
            classification="forbidden witness assembled by assumptions",
            exp_negative_inverse_seed=True,
            smoothness_on_positive_domain=True,
            derivative_hierarchy=True,
            positive_interior_nonzero=True,
            non_circular_source=False,
            forbidden_dependencies=(
                "imposed_derivative_hierarchy",
                "imposed_positive_interior",
                "target_blowup",
                "desired_conclusion",
            ),
            verdict="reject",
            note=(
                "The candidate has the requested analytic labels only because the "
                "hierarchy, interior positivity, and target role are imposed as "
                "assumptions."
            ),
        ),
    ]


def build_summary() -> dict[str, Any]:
    rows = [candidate.row() for candidate in candidate_families()]
    accepted = [row for row in rows if row["accepted"]]
    return {
        "contract": CONTRACT,
        "complete": False,
        "proof_claimed": False,
        "scope": "deterministic classifier for Navier-Stokes base exponential source candidates",
        "fail_closed": True,
        "route_decision": ROUTE_DECISION,
        "final_decision": ROUTE_DECISION,
        "accepted_source_count": len(accepted),
        "candidate_family_count": len(rows),
        "required_gates": list(REQUIRED_GATES),
        "forbidden_dependencies": list(FORBIDDEN_DEPENDENCIES),
        "accepted_families": [row["family"] for row in accepted],
        "rejected_families": [row["family"] for row in rows if not row["accepted"]],
        "option_b_closed": False,
        "clay_navier_stokes_promoted": False,
        "clay": False,
        "sprint110_base_exp_source_closed": False,
        "fail_closed_reason": (
            "No candidate supplies the exp-negative-inverse seed, positive-domain "
            "smoothness, derivative hierarchy, positive interior nonzero witness, "
            "and a non-circular source while avoiding forbidden dependencies."
        ),
        "control_card": {
            "O": "classify candidate base exponential source families",
            "R": "all six gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting summary JSON, rows JSON, CSV, and Markdown",
            "S": "five requested candidates evaluated in fixed order",
            "L": "acceptance is conjunction of gate_results",
            "P": ROUTE_DECISION,
            "G": "Clay Navier-Stokes promotion remains false",
            "F": "accepted_source_count is zero because every candidate fails non_circular_source or another required gate",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 110 Base Exponential Source Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Fail closed: `{str(summary['fail_closed']).lower()}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Candidate family count: `{summary['candidate_family_count']}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        f"- Clay: `{str(summary['clay']).lower()}`",
        "- Required gates: " + ", ".join(f"`{gate}`" for gate in summary["required_gates"]),
        "- Forbidden dependencies: "
        + ", ".join(f"`{item}`" for item in summary["forbidden_dependencies"]),
        "",
        "| Family | Accepted | Failed gates | Forbidden dependencies | Note |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in summary["rows"]:
        failed = "none" if not row["failed_gates"] else ", ".join(f"`{gate}`" for gate in row["failed_gates"])
        lines.append(
            f"| `{row['family']}` | `{str(row['accepted']).lower()}` | {failed} | `{row['forbidden_dependencies']}` | {row['note']} |"
        )
    lines.extend(["", summary["fail_closed_reason"]])
    return "\n".join(lines) + "\n"


def write_csv(out_dir: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = [
        "family_id",
        "family",
        "ansatz",
        "classification",
        "exp_negative_inverse_seed",
        "smoothness_on_positive_domain",
        "derivative_hierarchy",
        "positive_interior_nonzero",
        "non_circular_source",
        "no_forbidden_dependency",
        "forbidden_dependencies",
        "failed_gates",
        "accepted",
        "verdict",
        "note",
    ]
    with (out_dir / CSV_NAME).open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            csv_row = {key: row[key] for key in fieldnames}
            csv_row["failed_gates"] = "none" if not row["failed_gates"] else ";".join(row["failed_gates"])
            writer.writerow(csv_row)


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / ROWS_NAME).write_text(json.dumps(summary["rows"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_csv(out_dir, summary["rows"])
    (out_dir / REPORT_NAME).write_text(render_markdown(summary), encoding="utf-8")


def main() -> int:
    args = parse_args()
    summary = build_summary()
    out_dir = args.out_dir if args.out_dir.is_absolute() else args.repo_root / args.out_dir
    write_outputs(out_dir, summary)
    print(json.dumps({key: summary[key] for key in ("contract", "route_decision", "accepted_source_count", "clay")}, sort_keys=True))
    return 1 if summary["fail_closed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
