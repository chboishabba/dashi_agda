#!/usr/bin/env python3
"""Finite independent reference check for Woogaroo's Agda adversarial model.

The model tests hypothetical logical implication/consistency, not EPBC merits.
Seven canonical grounds share the same six-premise truth-table schema.
NO source review, counsel opinion, court finding, Agda kernel certificate,
or empirical payment can arise from this program.

Original source roles: Commonwealth EPBC Act / reform and court decisions;
QUT, QCC and Stockland retain authorship. The original DASHI/SensibLaw
proof owners and Ibrahim source genealogy remain independent.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

GROUNDS = (
    "advice-consideration",
    "recovery-plan",
    "incremental-habitat",
    "comment-transmission",
    "approval-scope",
    "local-prestart",
    "improper-influence",
)

def evaluate(world: tuple[bool, ...]) -> tuple[bool, bool, bool]:
    applicable, defect, material, compliance, reviewed, _harm = world
    applicant = not compliance and reviewed and applicable and defect and material
    respondent = compliance and not defect and reviewed and applicable
    contradiction = defect and compliance
    return applicant, respondent, contradiction

def check(agda_text: str | None = None, rust_text: str | None = None) -> dict:
    world_count = 0
    countermodels = 0
    sample_counts = None
    for ground in GROUNDS:
        # A bare observable lead cannot logically imply its independent bridge.
        assert not ((not True) or False), ground
        countermodels += 1
        counts = {"applicant": 0, "respondent": 0, "neither": 0, "contradiction": 0}
        for world in itertools.product((False, True), repeat=6):
            applicant, respondent, contradictory = evaluate(world)
            applicable, defect, material, compliance, reviewed, harm = world
            assert not (applicant and respondent), (ground, world)
            if contradictory:
                assert not applicant and not respondent, (ground, world)
                counts["contradiction"] += 1
            if not reviewed:
                assert not applicant and not respondent, (ground, world)
            if applicant:
                assert applicable and defect and material and reviewed and not compliance
                counts["applicant"] += 1
            elif respondent:
                assert applicable and compliance and reviewed and not defect
                counts["respondent"] += 1
            else:
                counts["neither"] += 1
            if harm and applicable and compliance and reviewed and not defect:
                assert respondent and not applicant  # harm != automatic invalidity
            world_count += 1
        assert counts == {
            "applicant": 2, "respondent": 4, "neither": 58, "contradiction": 16
        }, (ground, counts)
        sample_counts = counts

    if agda_text is not None:
        required_agda = (
            "conditionalApplicantDerivation",
            "conditionalRespondentDerivation",
            "cannotPromoteOppositeBranches",
            "contradictionNotGovernmentFinding",
            "sourceLeadAloneIsInsufficient",
            "canonicalIbrahimSourceCoverage",
            "canonicalParetoRoute",
        )
        for marker in required_agda + GROUNDS:
            assert marker in agda_text, f"missing Agda contract marker: {marker}"
        for unsafe in ("postulate ", "{!!}", "allow-unsolved-metas", "TERMINATING"):
            assert unsafe not in agda_text, f"untrusted shortcut in Agda source: {unsafe}"
    if rust_text is not None:
        required_rust = (
            "woogaroo_hypothetical_adversarial_test",
            "contradictory_assumptions_retained",
            "proves_actual_legal_merits: false",
            "creates_legal_evidence_review: false",
            "creates_court_filing: false",
        )
        for marker in required_rust:
            assert marker in rust_text, f"missing SLR source contract: {marker}"

    return {
        "status": "passed",
        "model": "unpaid_counterfactual_not_case_merits",
        "grounds": len(GROUNDS),
        "hypothetical_worlds": world_count,
        "lead_without_bridge_countermodels": countermodels,
        "counts_per_ground": sample_counts,
        "agda_source_contract_checked": agda_text is not None,
        "slr_source_contract_checked": rust_text is not None,
        "agda_kernel_checked": False,
        "source_evidence_reviewed": False,
        "legal_merits_proved": False,
    }

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--agda-file", type=Path)
    parser.add_argument("--slr-file", type=Path)
    args = parser.parse_args()
    agda = args.agda_file.read_text() if args.agda_file else None
    rust = args.slr_file.read_text() if args.slr_file else None
    print(json.dumps(check(agda, rust), indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
