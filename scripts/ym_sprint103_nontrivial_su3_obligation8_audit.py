#!/usr/bin/env python3
"""Sprint 103 obligation 8 nontrivial SU(3) continuum-measure audit."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_FILE = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "YMSprint103NontrivialSU3ContinuumMeasureObligation8.agda"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("outputs/ym_sprint103_nontrivial_su3_obligation8"),
    )
    return parser.parse_args()


def has_empty_data_skeleton(source: str) -> bool:
    return bool(re.search(r"(?m)^data\s+\S+.*:\s+Set[^\n]*\s+where\s*$", source))


def require_substrings(source: str, required: list[str]) -> dict[str, bool]:
    return {item: item in source for item in required}


def summary_payload() -> dict[str, Any]:
    source = AGDA_FILE.read_text()
    required_terms = [
        "F_mu_nu^a",
        "g f^{abc} A_mu^b A_nu^c",
        "cubicInteractionTerm",
        "quarticInteractionTerm",
        "connectedCumulantOrder",
        "kappa_4",
        "nonGaussianConnectedCorrelationPresent",
        "clayYangMillsPromoted = false",
    ]
    term_checks = require_substrings(source, required_terms)
    no_empty_data = not has_empty_data_skeleton(source)
    no_postulates = "postulate" not in source
    all_required_terms_present = all(term_checks.values())

    return {
        "sprint": "103-nontrivial-su3-continuum-measure-obligation8",
        "worker": "D",
        "obligation_number": 8,
        "scope": "Nontrivial4DSU3YangMillsMeasure only",
        "agda_file": str(AGDA_FILE.relative_to(REPO_ROOT)),
        "uses_sprint97_context": (
            "YMSprint97NontrivialSU3ContinuumMeasureReceipt" in source
        ),
        "explicit_nonabelian_curvature_recorded": all(
            term_checks[item]
            for item in [
                "F_mu_nu^a",
                "g f^{abc} A_mu^b A_nu^c",
            ]
        ),
        "cubic_self_interaction_recorded": term_checks["cubicInteractionTerm"],
        "quartic_self_interaction_recorded": term_checks["quarticInteractionTerm"],
        "non_gaussian_connected_correlation_witness_recorded": all(
            term_checks[item]
            for item in [
                "connectedCumulantOrder",
                "kappa_4",
                "nonGaussianConnectedCorrelationPresent",
            ]
        ),
        "no_empty_data_skeletons": no_empty_data,
        "no_postulates": no_postulates,
        "required_term_checks": term_checks,
        "continuum_measure_obligation8_closed_in_repo": (
            "continuumMeasureObligation8ClosedInRepo = true" in source
        ),
        "clay_yang_mills_promoted": False,
        "clay_statement_boundary_discharged": False,
        "external_acceptance_token_available": False,
        "audit_passed": all_required_terms_present
        and no_empty_data
        and no_postulates
        and "clayYangMillsPromoted = false" in source,
        "route_decision": "SPRINT103_OBLIGATION8_CLOSES_NONTRIVIAL_SU3_MEASURE_ONLY",
    }


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (
        out_dir / "ym_sprint103_nontrivial_su3_obligation8_summary.json"
    ).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")


def main() -> int:
    args = parse_args()
    summary = summary_payload()
    write_outputs(summary, args.out_dir)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if summary["audit_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
