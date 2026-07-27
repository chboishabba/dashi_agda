#!/usr/bin/env python3
"""Fail if the Clay-facing Stage-3 tranche introduces proof holes or postulates."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

FILES = [
    "DASHI/Physics/Closure/NSTriadKNLiteralDyadicShellConstants.agda",
    "DASHI/Physics/Closure/NSTriadKNCeilLogShellBounds.agda",
    "DASHI/Physics/Closure/NSTriadKNShellFactorTwo.agda",
    "DASHI/Physics/Closure/NSTriadKNLiteralDyadicConsequencesClosed.agda",
    "DASHI/Physics/Closure/NSTriadKNPhysicalOutputFiber.agda",
    "DASHI/Physics/Closure/NSTriadKNPhysicalTriadSymmetry.agda",
    "DASHI/Physics/Closure/NSTriadKNPhysicalSymmetryEnumerationClosure.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3ExactCarrier.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3FieldAlgebra.agda",
    "DASHI/Physics/Closure/NSTriadKNFrameFreeCoefficientRoute.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3RealityPhaseAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3GalerkinEquationAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNResonantNullGain.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3NullGainBridge.agda",
    "DASHI/Physics/Closure/NSTriadKNPhysicalTriadOrbitConstruction.agda",
    "DASHI/Physics/Closure/NSTriadKNEnergyCancellationAssembly.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3OrderedRealityCancellation.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3EnergyCancellation.agda",
    "DASHI/Physics/Closure/NSTriadKNPhaseFactorizationReduction.agda",
    "DASHI/Physics/Closure/NSTriadKNFiniteTrigonometricGalerkinEquivalence.agda",
    "DASHI/Physics/Closure/NSTriadKNCoarseGainDiagnostics.agda",
    "DASHI/Physics/Closure/NSTriadKNRefinedQuantitativeClassification.agda",
    "DASHI/Physics/Closure/NSTriadKNLegacyCoordinateInterpretationAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNCutoffUniformClasswiseEstimateProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNClasswiseAnalyticCutset.agda",
    "DASHI/Physics/Closure/NSTriadKNCubicQuadraticUniformGapNoGo.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticLyapunovDegreeAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticLyapunovEulerInvariantDecomposition.agda",
    "DASHI/Physics/Closure/NSTriadKNAdaptiveQuarticCoherenceCharts.agda",
    "DASHI/Physics/Closure/NSTriadKNPeriodicStokesModeDegeneracy.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticLyapunovCriticalProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticAnalyticFiniteSums.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticLiteralGalerkinDerivative.agda",
    "DASHI/Physics/Closure/NSTriadKNPeriodicUniformHarmonicAnalysis.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticSignedNearFarDecomposition.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticJointDominationFrontier.agda",
    "DASHI/Physics/Closure/NSTriadKNAdaptiveQuarticInvariantRegion.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticBKMExpenditure.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticStandardEndpoint.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticLyapunovEightStageProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNZeroCoherenceH3DiscriminantCounterexample.agda",
    "DASHI/Physics/Closure/NSTriadKNSignedUniformGapProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNArbitraryDataAprioriProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNSignedGapAprioriComposition.agda",
    "DASHI/Physics/Closure/NSTriadKNFourierLimitCompletionComposition.agda",
    "DASHI/Physics/Closure/NSTriadKNGalerkinCompletionEndpoint.agda",
    "DASHI/Physics/Closure/NSTriadKNPhysicalTriadFrontierProgram.agda",
]

PROVENANCE_FILES = [
    "DASHI/Physics/Closure/NSTriadKNQuarticLyapunovDegreeAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticLyapunovEulerInvariantDecomposition.agda",
    "DASHI/Physics/Closure/NSTriadKNAdaptiveQuarticCoherenceCharts.agda",
    "DASHI/Physics/Closure/NSTriadKNPeriodicStokesModeDegeneracy.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticLyapunovCriticalProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticAnalyticFiniteSums.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticLiteralGalerkinDerivative.agda",
    "DASHI/Physics/Closure/NSTriadKNPeriodicUniformHarmonicAnalysis.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticSignedNearFarDecomposition.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticJointDominationFrontier.agda",
    "DASHI/Physics/Closure/NSTriadKNAdaptiveQuarticInvariantRegion.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticBKMExpenditure.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticStandardEndpoint.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticLyapunovEightStageProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNZeroCoherenceH3DiscriminantCounterexample.agda",
]

LITERAL_MARKERS = (
    "{!!}",
    "?}",
    "{-# TERMINATING #-}",
    "{-# NON_TERMINATING #-}",
)

PROVENANCE_MARKERS = (
    "-- PROVENANCE",
    "-- Title:",
    "-- Venue/year:",
    "-- Relationship:",
)

POSTULATE_DECLARATION = re.compile(r"(?m)^\s*postulate(?:\s|$)")


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failures: list[str] = []

    for relative in FILES:
        path = root / relative
        if not path.is_file():
            failures.append(f"missing: {relative}")
            continue

        text = path.read_text(encoding="utf-8")
        if POSTULATE_DECLARATION.search(text):
            failures.append(f"{relative}: forbidden postulate declaration")

        for marker in LITERAL_MARKERS:
            if marker in text:
                failures.append(f"{relative}: forbidden marker {marker!r}")

        if text.count("(") != text.count(")"):
            failures.append(f"{relative}: unbalanced parentheses")
        if text.count("{") != text.count("}"):
            failures.append(f"{relative}: unbalanced braces")

    for relative in PROVENANCE_FILES:
        path = root / relative
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        for marker in PROVENANCE_MARKERS:
            if marker not in text:
                failures.append(
                    f"{relative}: missing provenance marker {marker!r}"
                )
        if "-- Authors:" not in text and "-- Author:" not in text:
            failures.append(f"{relative}: missing provenance author")
        if "-- DOI:" not in text and "-- Journal DOI:" not in text:
            failures.append(f"{relative}: missing DOI status")

    certificate = root / "scripts/ns_quartic_h3_zero_coherence_counterexample.py"
    if not certificate.is_file():
        failures.append("missing exact H^3 counterexample verifier")
    else:
        result = subprocess.run(
            [sys.executable, str(certificate)],
            cwd=root,
            check=False,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            failures.append(
                "exact H^3 counterexample verifier failed: "
                + (result.stderr.strip() or result.stdout.strip())
            )

    helical_check = root / "scripts/check_ns_helical_quartic_frontier.py"
    if not helical_check.is_file():
        failures.append("missing helical quartic frontier check")
    else:
        result = subprocess.run(
            [sys.executable, str(helical_check)],
            cwd=root,
            check=False,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            failures.append(
                "helical quartic frontier check failed: "
                + (result.stderr.strip() or result.stdout.strip())
            )

    if failures:
        for failure in failures:
            print(failure)
        return 1

    print(
        f"checked {len(FILES)} Clay-facing Stage-3 files and "
        f"{len(PROVENANCE_FILES)} provenance headers: no holes or postulates"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
