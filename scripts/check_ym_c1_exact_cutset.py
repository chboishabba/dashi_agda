#!/usr/bin/env python3
"""Fail-closed textual audit for the exact C1 Wilson/Hodge implementation cutset.

This is not a substitute for Agda kernel validation.  It prevents the focused
frontier files from silently losing required theorem surfaces, reintroducing
postulates/holes, or collapsing the periodic/open-boundary distinction.
"""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

FILES: dict[Path, tuple[str, ...]] = {
    YM / "BalabanSU2WilsonPlaquetteSecondJetExact.agda": (
        "plaquetteJetImaginaryFirstExact",
        "plaquetteJetRealSecondExact",
        "singlePlaquetteWilsonSecondVariationEqualsCurlNormSq",
        "reverseCurlIsNegative",
        "reverseOrientationPreservesCurlNormSq",
    ),
    YM / "BalabanConfiguredSide4PeriodicReindexingExact.agda": (
        "nextPrevious4",
        "previousNext4",
        "periodicForwardReindexing",
        "periodicBackwardReindexing",
        "periodicForwardBackwardSummationByParts",
    ),
    YM / "BalabanPath4SU2LiteralPlaquetteLiftExact.agda": (
        "physicalTangentAtSiteAxisAsLie3",
        "literalPlaquetteFourLinks",
        "literalPlaquetteLinearCurlEqualsForwardDifferenceCurl",
        "literalPlaquetteWilsonSecondVariationExact",
        "literalWilsonHessianPositivePlaneFoldExact",
        "literalWilsonHessianEqualsCurlEnergy",
    ),
    YM / "BalabanConfiguredSide4PeriodicVectorCalculusExact.agda": (
        "shiftForwardBackwardCommutes",
        "literalPeriodicDivergenceScalar",
        "literalNegativeForwardGradientScalar",
        "periodicDivergenceGradientAdjoint",
        "mixedForwardDifferenceSummationByParts",
        "curlCrossTermEqualsDivergenceCrossTerm",
    ),
    YM / "BalabanConfiguredSide4PeriodicHodgeExact.agda": (
        "positivePlaneSquareExpansion",
        "componentDivergenceEnergyExpansion",
        "fourAxisDiagonalOffDiagonalPartition",
        "componentDiscreteCurlDivergenceHodgeIdentity",
    ),
    YM / "BalabanPath4SU2PeriodicHodgeProducerExact.agda": (
        "literalPeriodicDivergence",
        "literalNegativeForwardGradient",
        "periodicDivergenceGradientAdjointSU2",
        "literalGaugeFixingEqualsDivergenceEnergy",
        "literalCurlEnergyComponentFold",
        "literalDivergenceEnergyComponentFold",
        "threeComponentDifferenceEnergyFoldExact",
        "discreteCurlDivergenceHodgeIdentity",
    ),
    YM / "BalabanConfiguredSide4PeriodicOpenEnergySeamExact.agda": (
        "periodicFibreDifferenceDecomposition",
        "forwardDerivativeEnergyOpenPlusWrap",
        "componentPeriodicDifferenceOpenPlusWrap",
        "physicalPeriodicDifferenceOpenPlusWrap",
        "hodgeRightHandSideMatchesPhysicalReferenceDifferenceEnergyPlusWrap",
        "unconditionalPeriodicEqualsOpenDifferenceEnergyLevel = conditional",
    ),
    YM / "BalabanPath4SU2WilsonGaugeOpenFoldExact.agda": (
        "literalWilsonGaugeEqualsPhysicalDifferencePlusBoundary",
        "hodgeRightHandSideMatchesPhysicalReferenceDifferenceEnergyWithBoundary",
        "unconditionalBoundaryFreeOpenFoldLevel = conditional",
    ),
    YM / "BalabanPath4SU2PeriodicReferenceHodgeExact.agda": (
        "physicalPeriodicWrapEnergyNonnegative",
        "literalWilsonGaugeEqualsPeriodicDifferenceEnergy",
        "physicalReferenceDifferenceBelowPeriodic",
        "literalPeriodicReferenceHodgeCoercivity",
        "literalPeriodicReferenceHodgeWithBlockPenalty",
    ),
    YM / "BalabanPath4SU2LiteralGaugeFixedHessianAdapterExact.agda": (
        "Path4SU2LiteralGaugeFixedHessianData",
        "wilsonHessianMatchesLiteral",
        "gaugeFixingMatchesLiteral",
        "literalGaugeFixedHessianPeriodicDecompositionExact",
        "uniformReferenceHodgeCoercivityFromLiteralProducer",
    ),
    YM / "BalabanSU2WilsonGaugeNormalizationClosureExact.agda": (
        "configuredWilsonGaugeNormalizationExact",
        "configuredReferenceConstantIsPurePoincare",
    ),
    YM / "BalabanConfiguredSide4TranslatedWilsonExtractionExact.agda": (
        "translatedBondRestrictionCommutesWithForwardShift",
        "translatedPlaquetteRestrictionCommutesWithCurl",
        "translatedWilsonPlaquetteHessianReindexing",
        "translatedWilsonPositivePlaneSiteFoldExact",
        "globalWilsonToLocalTranslatedBlock",
    ),
    YM / "BalabanArbitraryTranslatedOpenBlockWilsonExtractionExact.agda": (
        "translatedOpenPlaquetteFirstShift",
        "translatedOpenPlaquetteSecondShift",
        "translatedOpenPlaquetteCurlExact",
        "translatedOpenPlaquetteWilsonHessianExact",
        "globalWilsonToLocalTranslatedOpenBlock",
    ),
    YM / "BalabanC1ExactLemmaAliases.agda": (
        "divergenceSquareExpansion",
        "componentDifferenceEnergyAxisSiteFold",
        "componentDifferenceEnergyMatchesBondReferenceDifferenceEnergy",
    ),
    YM / "BalabanPhysicalC1CompletionLedger.agda": (
        "literalSU2WilsonSecondJetLevel = machineChecked",
        "configuredPeriodicHodgeIdentityLevel = machineChecked",
        "literalWilsonGaugeOpenFoldWithBoundaryLevel = machineChecked",
        "arbitraryLatticeOpenBlockWilsonExtractionLevel = machineChecked",
        "repositorySUNWilsonActionHessianAdapterLevel = conditional",
        "branchHeadAuthoritativeTypecheckLevel = conditional",
    ),
}

FORBIDDEN = (
    "postulate",
    "{!!}",
    "{-# TERMINATING #-}",
    "{-# NON_TERMINATING #-}",
    "= _",
)


def fail(message: str) -> None:
    print(f"C1 exact-cutset audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    for path, required in FILES.items():
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        text = path.read_text(encoding="utf-8")
        for token in FORBIDDEN:
            if token in text:
                fail(f"forbidden token {token!r} in {path.relative_to(ROOT)}")
        for theorem in required:
            if theorem not in text:
                fail(f"missing {theorem!r} in {path.relative_to(ROOT)}")

    print(
        "Exact C1 SU(2) Wilson jet, periodic Hodge algebra, open-boundary seam, "
        "normalization, and translated extraction surfaces are present and hole-free."
    )


if __name__ == "__main__":
    main()
