#!/usr/bin/env python3
"""Fail closed on constructive-real comparison and output-relocation closure."""
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
    "DASHI/Physics/Closure/NSTriadKNRationalFiniteGeometricEnvelope.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationIntegerGeometricEnvelope.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationPositiveKernelMajorant.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationUnitWeightShellSchur.agda",
    "DASHI/Physics/Closure/NSTriadKNRationalFiniteSignedMajorant.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationConditionalCutoffUniformClosure.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationEmbeddedEnvelopeClosure.agda",
    "DASHI/Physics/Closure/NSTriadKNConstructiveRealSpineOutputEnvelopeAdapter.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationPowerMonotonicityBridge.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationAbsoluteCoefficientBridge.agda",
    "DASHI/Physics/Closure/NSTriadKNConstructiveRealSpineOutputRelocationDerivedClosure.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationFiniteSquaredCoefficientMajorant.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationSquaredToAbsoluteBridge.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationFiniteToNativeSquaredBridge.agda",
    "DASHI/Physics/Closure/NSTriadKNConstructiveRealSpineOutputRelocationSquaredClosure.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationKatoPonceBonyScopeAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNConstructiveRealSpineOutputDecayIntervalDerivation.agda",
    "DASHI/Physics/Closure/NSTriadKNConstructiveRealSpineOrderedFieldCapabilityAdapter.agda",
    "DASHI/Physics/Closure/NSTriadKNConstructiveRealSpineBaseTwoExponentialAdapter.agda",
    "DASHI/Physics/Closure/NSTriadKNConstructiveRealSpineOutputDecayFromOrderedField.agda",
    "DASHI/Physics/Closure/NSTriadKNConstructiveRealSpineOutputRelocationFrontierClosure.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationSquaredCoefficientIntegration.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationCutoffUniformArchetypeProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNAffineResolvedFamilyReduction.agda",
    "DASHI/Physics/Closure/NSTriadKNDongLiFrequencyLocalizedCoercivityAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNStage3ConstructiveSeriesOrientationIntegration.agda",
)

VERIFIERS = (
    "scripts/ns_stage3_murray_source_pin_audit.py",
    "scripts/ns_stage3_power_law_orientation_audit.py",
    "scripts/ns_stage3_output_relocation_farkas_audit.py",
    "scripts/ns_stage3_output_relocation_unit_weight_audit.py",
    "scripts/ns_stage3_output_relocation_integer_envelope_audit.py",
    "scripts/ns_stage3_output_relocation_majorant_audit.py",
    "scripts/ns_stage3_output_relocation_derived_bridge_audit.py",
    "scripts/ns_stage3_output_relocation_squared_coefficient_audit.py",
    "scripts/ns_stage3_small_epsilon_affine_audit.py",
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
        f"checked Murray thesis pin, Dong Li coercivity boundary and "
        f"output-relocation closure tranche: {len(FILES)} Agda modules, "
        f"{len(VERIFIERS)} exact verifiers, provenance and static safety; "
        "source-style homogeneity is rejected, unit weights close Check A, "
        "the rational 128/93 kernel and native theorem composition are closed, "
        "the coefficient estimate is reduced to an exact finite squared fibre "
        "realization plus ordered-square transport, base-two powers are built "
        "from the native exponential, endpoint inequalities are derived from "
        "5/2<s<3, one affine family is resolved leaving 21 live slots, and only "
        "concrete backend/log-two/fibre-identification data remain fail-closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
