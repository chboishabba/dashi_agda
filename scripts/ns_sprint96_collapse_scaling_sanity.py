#!/usr/bin/env python3
"""Sprint 96 NS Option B K* collapse scaling sanity script.

This script is a deterministic sanity ledger, not a proof search.  It evaluates
named candidate K*(t) collapse laws against the required Option B gates and
fails closed unless one candidate supplies every gate without forbidden
dependencies.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint96_collapse_scaling_sanity"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint96_collapse_scaling_sanity")
SUMMARY_NAME = "ns_sprint96_collapse_scaling_sanity_summary.json"
ROWS_NAME = "ns_sprint96_collapse_scaling_sanity_rows.json"
REPORT_NAME = "ns_sprint96_collapse_scaling_sanity.md"

REQUIRED_GATES = (
    "finite_time_collapse",
    "leray_energy_compatible",
    "excludes_conditional_lower_bound",
    "singularity_extraction",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "clay_claim",
    "target_absorption",
    "desired_conclusion",
    "h1_continuation",
    "theta_preservation",
    "option_c_conditional",
    "conditional_regular",
    "general_data_regular",
    "blowup_construction_assumed",
    "target_blowup",
    "bkm_failure_assumed",
    "serrin_failure_assumed",
    "desired_singularity",
    "negated_conditional_criterion_without_mechanism",
)


@dataclass(frozen=True)
class Candidate:
    candidate_id: str
    name: str
    law: str
    limit_as_t_to_T: str
    monotonicity: str
    finite_time_collapse: bool
    leray_energy_compatible: bool
    excludes_conditional_lower_bound: bool
    singularity_extraction: bool
    forbidden_dependencies: tuple[str, ...]
    note: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def accepted(self) -> bool:
        return all(
            (
                self.finite_time_collapse,
                self.leray_energy_compatible,
                self.excludes_conditional_lower_bound,
                self.singularity_extraction,
                self.no_forbidden_dependency,
            )
        )

    def row(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["forbidden_dependencies"] = (
            "none" if not self.forbidden_dependencies else ";".join(self.forbidden_dependencies)
        )
        payload["no_forbidden_dependency"] = self.no_forbidden_dependency
        payload["accepted"] = self.accepted
        payload["gate_results"] = {
            "finite_time_collapse": self.finite_time_collapse,
            "leray_energy_compatible": self.leray_energy_compatible,
            "excludes_conditional_lower_bound": self.excludes_conditional_lower_bound,
            "singularity_extraction": self.singularity_extraction,
            "no_forbidden_dependency": self.no_forbidden_dependency,
        }
        payload["failed_gates"] = [
            gate for gate, passed in payload["gate_results"].items() if not passed
        ]
        return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def candidates() -> list[Candidate]:
    return [
        Candidate(
            candidate_id="C0",
            name="constant lower-bound",
            law="K*(t) = K0 > 0 for 0 <= t < T",
            limit_as_t_to_T="K0",
            monotonicity="constant",
            finite_time_collapse=False,
            leray_energy_compatible=True,
            excludes_conditional_lower_bound=False,
            singularity_extraction=False,
            forbidden_dependencies=(),
            note=(
                "Compatible with a lower-bound picture but does not collapse to zero; "
                "it therefore cannot drive Option B."
            ),
        ),
        Candidate(
            candidate_id="A1",
            name="algebraic collapse to 0",
            law="K*(t) = c (T - t)^alpha, alpha > 0",
            limit_as_t_to_T="0",
            monotonicity="strictly decreasing for alpha > 0",
            finite_time_collapse=True,
            leray_energy_compatible=False,
            excludes_conditional_lower_bound=False,
            singularity_extraction=False,
            forbidden_dependencies=(),
            note=(
                "Supplies a formal collapse rate, but this sanity ledger has no "
                "independent Leray-compatible construction, lower-bound exclusion, "
                "or singularity extraction."
            ),
        ),
        Candidate(
            candidate_id="L1",
            name="logarithmic slow collapse",
            law="K*(t) = c / log(e + 1/(T - t))",
            limit_as_t_to_T="0",
            monotonicity="decreasing near T",
            finite_time_collapse=True,
            leray_energy_compatible=False,
            excludes_conditional_lower_bound=False,
            singularity_extraction=False,
            forbidden_dependencies=(),
            note=(
                "A slower collapse ansatz still lacks an independent energy "
                "compatibility mechanism and does not defeat conditional lower-bound criteria."
            ),
        ),
        Candidate(
            candidate_id="O1",
            name="oscillatory candidate",
            law="K*(t) = c (T - t)^alpha (1 + beta sin(omega log(1/(T - t))))",
            limit_as_t_to_T="0 only under amplitude restrictions",
            monotonicity="oscillatory",
            finite_time_collapse=True,
            leray_energy_compatible=False,
            excludes_conditional_lower_bound=False,
            singularity_extraction=False,
            forbidden_dependencies=("desired_singularity",),
            note=(
                "Oscillation adds no accepted extraction mechanism here and is rejected "
                "for relying on a target singularity dependency."
            ),
        ),
    ]


def build_summary() -> dict[str, Any]:
    rows = [candidate.row() for candidate in candidates()]
    accepted = [row for row in rows if row["accepted"]]
    fail_closed = len(accepted) == 0
    return {
        "contract": CONTRACT,
        "complete": False,
        "proof_claimed": False,
        "scope": "deterministic scaling sanity ledger for Option B candidate K*(t) laws",
        "fail_closed": fail_closed,
        "route_decision": "FAIL_CLOSED" if fail_closed else "CANDIDATE_ACCEPTED",
        "final_decision": "FAIL_CLOSED" if fail_closed else "REVIEW_ACCEPTED_CANDIDATE",
        "accepted_source_count": len(accepted),
        "candidate_count": len(rows),
        "required_gates": list(REQUIRED_GATES),
        "forbidden_dependencies": list(FORBIDDEN_DEPENDENCIES),
        "accepted_candidates": [row["candidate_id"] for row in accepted],
        "clay_navier_stokes_promoted": False,
        "option_b_closed": bool(accepted),
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 96 Collapse Scaling Sanity",
        "",
        f"- Contract: `{summary['contract']}`",
        "- Scope: deterministic sanity evaluation of candidate `K*(t)` collapse laws for Option B.",
        "- Proof claimed: `false`",
        f"- Fail closed: `{str(summary['fail_closed']).lower()}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Candidate count: `{summary['candidate_count']}`",
        f"- Final decision: `{summary['final_decision']}`",
        "- Required gates: " + ", ".join(f"`{gate}`" for gate in summary["required_gates"]),
        "- Forbidden dependencies: "
        + ", ".join(f"`{dependency}`" for dependency in summary["forbidden_dependencies"]),
        "",
        "| Candidate | Law | Accepted | Failed gates | Forbidden dependencies | Note |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in summary["rows"]:
        failed = "none" if not row["failed_gates"] else ", ".join(f"`{gate}`" for gate in row["failed_gates"])
        forbidden = row["forbidden_dependencies"]
        lines.append(
            "| "
            + " | ".join(
                [
                    f"`{row['candidate_id']}` {row['name']}",
                    f"`{row['law']}`",
                    f"`{str(row['accepted']).lower()}`",
                    failed,
                    f"`{forbidden}`",
                    row["note"],
                ]
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "The ledger is fail-closed because no candidate satisfies all required gates without a forbidden dependency.",
        ]
    )
    return "\n".join(lines) + "\n"


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (out_dir / ROWS_NAME).write_text(
        json.dumps(summary["rows"], indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (out_dir / REPORT_NAME).write_text(render_markdown(summary), encoding="utf-8")


def main() -> int:
    args = parse_args()
    _repo_root = args.repo_root.resolve()
    summary = build_summary()
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
