#!/usr/bin/env python3
"""Fail-closed textual audit for the explicit P1--P5 Yang--Mills frontier.

This script is intentionally narrower than Agda kernel validation.  It checks
that the exact reductions and the honest producer ledger remain present, and
rejects postulates, holes, unsafe termination and underscore proof bodies in the
new frontier modules.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

FILES: dict[Path, tuple[str, ...]] = {
    YM / "BalabanSU2RationalAdjointRadiusExact.agda": (
        "adjointDisplacementWithUnitDefectExact",
        "adjointDisplacementUnitExact",
        "adjointDisplacementPlusDiscardedSquareExact",
        "adjointDisplacementRadiusBound",
        "su2PhysicalLinkRadiusProducerLevel = conditional",
    ),
    YM / "BalabanSU2RationalWilsonLargeFieldGapExact.agda": (
        "unitChordalEqualsTwiceTraceDeficit",
        "wilsonActionEqualsHalfBetaChordal",
        "localWilsonActionGap",
        "largeFieldActionLowerBoundFromWitnesses",
        "largeFieldDuplicateFreeWitnessGeometryLevel = conditional",
    ),
    YM / "BalabanClayP1BackgroundStabilityExact.agda": (
        "RegularBackgroundConstruction",
        "backgroundHessianExact",
        "backgroundRelativeFormSmallness",
        "smallBackgroundOneThirtySecondCoercivity",
        "p1MinimizingBackgroundProducerLevel = conditional",
        "p1FiveUniformComponentEstimatesLevel = conditional",
    ),
    YM / "BalabanClayP2LargeFieldStepVExact.agda": (
        "GaugeInvariantBadBlockDecomposition",
        "LargeFieldActivityFactorization",
        "uniformFiniteVolumeKoteckyPreiss",
        "etaGapPositive",
        "p2PhysicalActivityShellProducerLevel = conditional",
        "p2InfiniteClusterAndCorrelationProducerLevel = conditional",
    ),
    YM / "BalabanClayP3PhysicalOneStepTransferExact.agda": (
        "ExactOneStepIntegral",
        "ExactNonlinearFluctuationCoordinates",
        "ExactSchurComplement",
        "oneStepPerturbationBound",
        "oneStepPhysicalCoercivityTransfer",
        "noGeneratedGaugeBosonMass",
        "RunningCouplingRecursion",
        "p3FivePhysicalComponentEstimateProducerLevel = conditional",
    ),
    YM / "BalabanClayP4DyadicCoercivityBudgetExact.agda": (
        "lossBudgetIdentity",
        "lossPartialSumBelowOneSixtyFourth",
        "uniformOneSixtyFourthCoercivity",
        "physicalOneStepLossEstimateLevel = conditional",
    ),
    YM / "BalabanClayP4CommonParameterDomainExact.agda": (
        "canonicalClayParameters",
        "canonicalBackgroundBudgetIdentity",
        "canonicalDomainIsCommon",
        "canonicalBackgroundConstraintProducerLevel = conditional",
        "canonicalContinuumConstraintProducerLevel = conditional",
    ),
    YM / "BalabanClayP5ContinuumMassGapExact.agda": (
        "AllScaleFiniteVolumeConstruction",
        "ThermodynamicLimit",
        "ContinuumLimit",
        "OsterwalderSchraderLimit",
        "physicalConnectedCorrelationBound",
        "positivePhysicalSpectralGap",
        "InteractingNontriviality",
        "p5NontrivialityProducerLevel = conditional",
    ),
    YM / "BalabanClayFrontierCompletionLedger.agda": (
        "uniformOneSixtyFourthCoercivityLevel = machineChecked",
        "p1NonlinearMinimizingBackgroundLevel = conditional",
        "p2PhysicalActivityAndRootedShellEstimateLevel = conditional",
        "p3ConstructiveSchurComplementPropagatorLevel = conditional",
        "p5ContinuumOSAndNontrivialityLevel = conditional",
        "constructiveConfiguredFiniteInverseLevel = conditional",
        "branchHeadAuthoritativeAgda29TypecheckLevel = conditional",
    ),
}

FORBIDDEN_PATTERNS = (
    (re.compile(r"(?m)^\s*postulate\b"), "postulate declaration"),
    (re.compile(r"\{\!\!\}"), "Agda hole"),
    (re.compile(r"\{-#\s*(?:NON_)?TERMINATING\s*#-\}"), "unsafe termination pragma"),
    (re.compile(r"=\s*_\s*(?:\n|$)"), "underscore proof body"),
)


def fail(message: str) -> None:
    print(f"Clay frontier audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    for path, required in FILES.items():
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        text = path.read_text(encoding="utf-8")
        for pattern, label in FORBIDDEN_PATTERNS:
            if pattern.search(text):
                fail(f"forbidden {label} in {path.relative_to(ROOT)}")
        for token in required:
            if token not in text:
                fail(f"missing {token!r} in {path.relative_to(ROOT)}")

    aggregate = YM / "ConstructiveYangMillsNextSurface.agda"
    aggregate_text = aggregate.read_text(encoding="utf-8")
    for module in (
        "BalabanSU2RationalAdjointRadiusExact",
        "BalabanSU2RationalWilsonLargeFieldGapExact",
        "BalabanClayP1BackgroundStabilityExact",
        "BalabanClayP2LargeFieldStepVExact",
        "BalabanClayP3PhysicalOneStepTransferExact",
        "BalabanClayP4DyadicCoercivityBudgetExact",
        "BalabanClayP4CommonParameterDomainExact",
        "BalabanClayP5ContinuumMassGapExact",
        "BalabanClayFrontierCompletionLedger",
    ):
        if module not in aggregate_text:
            fail(f"aggregate does not import {module}")

    print(
        "P1--P5 exact reductions, numerical budgets, endpoint surfaces, and "
        "honest conditional producer ledger are present and hole-free."
    )


if __name__ == "__main__":
    main()
