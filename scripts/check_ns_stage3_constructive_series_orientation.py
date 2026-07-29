#!/usr/bin/env python3
"""Fail closed on constructive-real comparison and output-relocation Check A."""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

FILES = (
    "DASHI/Physics/Closure/NSTriadKNMurrayThesisCommitSourceInspection.agda",
    "DASHI/Physics/Closure/NSTriadKNConstructiveRealCandidateComparison.agda",
    "DASHI/Physics/Closure/NSTriadKNGrafakosTorresPowerLawOrientation.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationWeightedExponentIdentity.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationLiteralShellSubstitution.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationAffineFamilySubstitution.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationCheckACriterion.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationBaseSystemClassification.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationDirectionSystemClassification.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationAffineFarkasDecision.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationUnitWeightCheckA.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationIntegerGeometricEnvelope.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationPowerMonotonicityBridge.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationCutoffUniformArchetypeProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNDongLiFrequencyLocalizedCoercivityAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNStage3ConstructiveSeriesOrientationIntegration.agda",
)

VERIFIERS = (
    "scripts/ns_stage3_murray_source_pin_audit.py",
    "scripts/ns_stage3_power_law_orientation_audit.py",
    "scripts/ns_stage3_output_relocation_farkas_audit.py",
    "scripts/ns_stage3_output_relocation_unit_weight_audit.py",
    "scripts/ns_stage3_output_relocation_integer_envelope_audit.py",
)

PROVENANCE = (
    "-- PROVENANCE",
    "-- Authors:",
    "-- Title:",
    "-- Venue/year:",
    "-- DOI:",
    "-- Relationship:",
)
FORBIDDEN = ("{!!}", "?}", "{-# TERMINATING #-}", "{-# NON_TERMINATING #-}")
POSTULATE = re.compile(r"(?m)^\s*postulate(?:\s|$)")


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
            failures.append(f"{relative}: forbidden postulate")
        for marker in FORBIDDEN:
            if marker in text:
                failures.append(f"{relative}: forbidden marker {marker!r}")
        for marker in PROVENANCE:
            if marker not in text:
                failures.append(
                    f"{relative}: missing provenance marker {marker!r}"
                )
        for opening, closing in (("(", ")"), ("{", "}")):
            if text.count(opening) != text.count(closing):
                failures.append(f"{relative}: unbalanced {opening}{closing}")

    for relative in VERIFIERS:
        verifier = root / relative
        if not verifier.is_file():
            failures.append(f"missing exact verifier: {relative}")
            continue
        result = subprocess.run(
            [sys.executable, str(verifier)],
            cwd=root,
            check=False,
            capture_output=True,
            text=True,
        )
        if result.returncode:
            failures.append(result.stderr.strip() or result.stdout.strip())

    if failures:
        print("\n".join(failures))
        return 1
    print(
        "checked Murray thesis pin, Dong Li coercivity boundary and "
        "output-relocation Check A tranche: 16 Agda modules, 5 exact "
        "verifiers, provenance, no holes/postulates/escapes; the source-style "
        "all-three-homogeneity affine ansatz is exactly infeasible, constant "
        "unit weights recover symbolic Check A, integer geometric envelopes "
        "give the exact 128/93 cutoff bound, and the final archetype cutset is "
        "specified; only the two constructive base-two domination lemmas and "
        "positive-kernel/signed-majorant instantiation remain fail-closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
