#!/usr/bin/env python3
"""Fail closed on the output-relocation falsification and closure experiment."""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

FILES = (
    "DASHI/Physics/Closure/NSTriadKNInageHighHighComparatorAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3RelocationInstantiation.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationWeightedExponentIdentity.agda",
    "DASHI/Physics/Closure/NSTriadKNStage3OutputRelocationVerticalSlice.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationAffineFarkasDecision.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationUnitWeightCheckA.agda",
    "DASHI/Physics/Closure/NSTriadKNRationalFiniteGeometricEnvelope.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationIntegerGeometricEnvelope.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationPositiveKernelMajorant.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationUnitWeightShellSchur.agda",
    "DASHI/Physics/Closure/NSTriadKNRationalFiniteSignedMajorant.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationConditionalCutoffUniformClosure.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationEmbeddedEnvelopeClosure.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationPowerMonotonicityBridge.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationCutoffUniformArchetypeProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNAffineResolvedFamilyReduction.agda",
    "DASHI/Physics/Closure/NSTriadKNStage3OutputRelocationExperimentIntegration.agda",
)

VERIFIERS = (
    "scripts/ns_stage3_output_relocation_vertical_slice_audit.py",
    "scripts/ns_stage3_output_relocation_farkas_audit.py",
    "scripts/ns_stage3_output_relocation_unit_weight_audit.py",
    "scripts/ns_stage3_output_relocation_integer_envelope_audit.py",
    "scripts/ns_stage3_output_relocation_majorant_audit.py",
    "scripts/ns_stage3_small_epsilon_affine_audit.py",
)

PROVENANCE = (
    "-- PROVENANCE",
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
                failures.append(f"{relative}: missing provenance marker {marker!r}")
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
        f"checked output-relocation experiment: {len(FILES)} Agda modules, "
        f"{len(VERIFIERS)} exact audits, provenance and static safety; "
        "source-style affine homogeneity is rejected, unit weights and the "
        "rational/embedded 128/93 majorant programmes are closed, one affine "
        "family is resolved leaving 21 live slots, and only the concrete "
        "ordered carrier/H^s/coefficient bridge and operator theorem remain "
        "fail-closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
