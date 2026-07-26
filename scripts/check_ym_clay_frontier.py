#!/usr/bin/env python3
"""Fail-closed textual audit for the explicit P1--P5 Yang--Mills frontier.

The script checks declaration integrity and the honesty ledger.  It does not
replace the Agda kernel.  The constructive configured Green closure is delegated
to its own stricter audit so the frontier and finite inverse cuts cannot drift.
"""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

FILES: dict[Path, tuple[str, ...]] = {
    YM / "BalabanSU2RationalAdjointRadiusExact.agda": (
        "adjointDisplacementWithUnitDefectExact",
        "adjointDisplacementRadiusBound",
        "su2PhysicalLinkRadiusProducerLevel = conditional",
    ),
    YM / "BalabanSU2RationalWilsonLargeFieldGapExact.agda": (
        "unitChordalEqualsTwiceTraceDeficit",
        "localWilsonActionGap",
        "largeFieldActionLowerBoundFromWitnesses",
        "largeFieldDuplicateFreeWitnessGeometryLevel = conditional",
    ),
    YM / "BalabanClayP1BackgroundStabilityExact.agda": (
        "RegularBackgroundConstruction",
        "backgroundRelativeFormSmallness",
        "smallBackgroundOneThirtySecondCoercivity",
        "p1MinimizingBackgroundProducerLevel = conditional",
        "p1FiveUniformComponentEstimatesLevel = conditional",
    ),
    YM / "BalabanClayP2LargeFieldStepVExact.agda": (
        "GaugeInvariantBadBlockDecomposition",
        "LargeFieldActivityFactorization",
        "uniformFiniteVolumeKoteckyPreiss",
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
        "configuredMatrixActionLinearityLevel = machineChecked",
        "configuredGreenMatrixInverseProductLevel = machineChecked",
        "configuredPhysicalGreenNormLevel = machineChecked",
        "constructiveConfiguredFiniteInverseLevel = machineChecked",
        "p1NonlinearMinimizingBackgroundLevel = conditional",
        "p2PhysicalActivityAndRootedShellEstimateLevel = conditional",
        "p3ExactConstrainedIntegralCoordinatesLevel = conditional",
        "p4CanonicalCommonDomainInhabitationLevel = conditional",
        "p5ContinuumOSAndNontrivialityLevel = conditional",
        "branchHeadAuthoritativeAgda29TypecheckLevel = conditional",
    ),
}

FORBIDDEN = (
    (re.compile(r"(?m)^\s*postulate\b"), "postulate declaration"),
    (re.compile(r"\{\!\!\}"), "Agda hole"),
    (re.compile(r"\{-#\s*(?:NON_)?TERMINATING\s*#-\}"), "unsafe termination pragma"),
    (re.compile(r"=\s*_\s*(?:\n|$)"), "underscore proof body"),
)


def fail(message: str) -> None:
    print(f"Clay frontier audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    for path, tokens in FILES.items():
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        text = path.read_text(encoding="utf-8")
        for pattern, label in FORBIDDEN:
            if pattern.search(text):
                fail(f"forbidden {label} in {path.relative_to(ROOT)}")
        for token in tokens:
            if token not in text:
                fail(f"missing {token!r} in {path.relative_to(ROOT)}")

    subprocess.run(
        [sys.executable, str(ROOT / "scripts/check_ym_configured_green_exact.py")],
        cwd=ROOT,
        check=True,
    )

    print(
        "P1--P5 reductions and conditional physical producers remain explicit; "
        "the configured side-four matrix action, two-sided rational inverse and "
        "factor-16 norm certificate are closed by the focused Green audit."
    )


if __name__ == "__main__":
    main()
