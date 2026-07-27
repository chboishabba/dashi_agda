#!/usr/bin/env python3
"""Fail closed on the helical quartic candidate and reconnaissance tranche."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

FILES = [
    "DASHI/Physics/Closure/NSTriadKNPeriodicHelicalFourierInfrastructure.agda",
    "DASHI/Physics/Closure/NSTriadKNHelicityPerturbedOperatorQuadratic.agda",
    "DASHI/Physics/Closure/NSTriadKNGlobalHelicityH3DiscriminantCounterexample.agda",
    "DASHI/Physics/Closure/NSTriadKNLocalizedHelicityCommutatorProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNAdaptiveLinearHelicalProbeProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNHelicalDiscriminantMarginProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNLocalizedHelicityExactReconnaissance.agda",
    "DASHI/Physics/Closure/NSTriadKNFixedSymbolBalancedFamilyReconnaissance.agda",
    "DASHI/Physics/Closure/NSTriadKNTriadPhaseCoherenceFallback.agda",
    "DASHI/Physics/Closure/NSTriadKNHelicalCandidateDecisionFork.agda",
]

PROVENANCE_MARKERS = (
    "-- PROVENANCE",
    "-- Title:",
    "-- Venue/year:",
    "-- Relationship:",
)

FORBIDDEN = (
    "{!!}",
    "?}",
    "{-# TERMINATING #-}",
    "{-# NON_TERMINATING #-}",
)

POSTULATE = re.compile(r"(?m)^\s*postulate(?:\s|$)")


def run_verifier(root: Path, relative: str, label: str) -> str | None:
    verifier = root / relative
    if not verifier.is_file():
        return f"missing {label}"
    result = subprocess.run(
        [sys.executable, str(verifier)],
        cwd=root,
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode:
        return f"{label} failed: " + (result.stderr.strip() or result.stdout.strip())
    return None


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failures: list[str] = []

    for relative in FILES:
        path = root / relative
        if not path.is_file():
            failures.append(f"missing: {relative}")
            continue
        text = path.read_text(encoding="utf-8")
        if POSTULATE.search(text):
            failures.append(f"{relative}: forbidden postulate declaration")
        for marker in FORBIDDEN:
            if marker in text:
                failures.append(f"{relative}: forbidden marker {marker!r}")
        for opening, closing in (("(", ")"), ("{", "}")):
            if text.count(opening) != text.count(closing):
                failures.append(
                    f"{relative}: unbalanced {opening}{closing} delimiters"
                )
        for marker in PROVENANCE_MARKERS:
            if marker not in text:
                failures.append(
                    f"{relative}: missing provenance marker {marker!r}"
                )
        if "-- Authors:" not in text and "-- Author:" not in text:
            failures.append(f"{relative}: missing provenance author")
        if "-- DOI:" not in text:
            failures.append(f"{relative}: missing DOI status")

    for relative, label in (
        (
            "scripts/ns_quartic_helicity_perturbed_counterexample.py",
            "global-helicity exact verifier",
        ),
        (
            "scripts/ns_quartic_localized_helicity_reconnaissance.py",
            "localized-helicity reconnaissance verifier",
        ),
    ):
        failure = run_verifier(root, relative, label)
        if failure is not None:
            failures.append(failure)

    if failures:
        print("\n".join(failures))
        return 1

    print(
        f"checked {len(FILES)} helical quartic files: no holes or postulates; "
        "global and localized exact verifiers passed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
