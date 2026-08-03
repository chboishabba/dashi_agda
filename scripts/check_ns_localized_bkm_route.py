#!/usr/bin/env python3
"""Fail-closed static audit for the exact localized-BKM construction tranche.

This checker verifies primary-source attribution, the exact periodic LP/Bony
support algebra, the cutoff-indexed depth replacement, the finite residue-gap
authority, the Luo cutoff-majorant theorem, and preservation of all physical
BKM/Clay fail-closed gates.  It is not an Agda typecheck.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLOSURE = ROOT / "DASHI" / "Physics" / "Closure"

FILES = {
    "inventory": CLOSURE / "NSTriadKNLittlewoodPaleyInfrastructureInventory.agda",
    "sources": CLOSURE / "NSTriadKNLocalizedBKMSourceAndTargetAudit.agda",
    "assembly": CLOSURE / "NSTriadKNFiniteLowUniformHighAssembly.agda",
    "periodic_lp": CLOSURE / "NSTriadKNPeriodicLittlewoodPaleyBonyExact.agda",
    "depth_exact": CLOSURE / "NSTriadKNProfileDepthGeometryCutoffIndexedExact.agda",
    "residue_exact": CLOSURE / "NSTriadKNResidueScaleOperatorGapExact.agda",
    "luo": CLOSURE / "NSTriadKNLuoExplicitCutoffLocalizedCriterionExact.agda",
    "compatibility": CLOSURE / "NSTriadKNBlockerToLocalizedBKMCompatibility.agda",
    "authority": CLOSURE / "NSTriadKNAnalyticBlockerAuthorityAudit.agda",
    "integration": CLOSURE / "NSTriadKNLocalizedBKMRouteIntegration.agda",
    "forced_tail": CLOSURE / "NSTriadKNProfileCrossForcedTailRefinement.agda",
    "legacy_depth": CLOSURE / "NSTriadKNProfileDepthGeometryBase.agda",
    "weight_bridge": CLOSURE / "NSTriadKNProfileCrossWeightBridge.agda",
    "pair_bounds": CLOSURE / "NSTriadKNPairIncidenceProfileBounds.agda",
}

NEW_AXIOM_FREE_FILES = (
    "inventory",
    "sources",
    "assembly",
    "periodic_lp",
    "depth_exact",
    "residue_exact",
    "luo",
    "compatibility",
    "authority",
    "integration",
)


def fail(message: str) -> None:
    print(f"FAIL: {message}")
    raise SystemExit(1)


def require(text: str, needle: str, label: str) -> None:
    if needle not in text:
        fail(f"{label}: missing {needle!r}")


def forbid(text: str, needle: str, label: str) -> None:
    if needle in text:
        fail(f"{label}: forbidden {needle!r}")


def load_files() -> dict[str, str]:
    loaded: dict[str, str] = {}
    for name, path in FILES.items():
        if not path.is_file():
            fail(f"missing required file: {path.relative_to(ROOT)}")
        loaded[name] = path.read_text(encoding="utf-8")
    return loaded


def main() -> int:
    text = load_files()

    print("[1/10] Checking primary-source provenance and route semantics...")
    sources = text["sources"]
    for doi in (
        "10.1007/BF01212349",
        "10.1007/s00021-014-0167-4",
        "10.48550/arXiv.0708.3067",
        "10.1017/S0013091525100813",
        "10.48550/arXiv.1507.06611",
        "10.1007/s00220-007-0319-y",
        "10.1007/s00021-019-0411-z",
        "10.48550/arXiv.1803.05569",
    ):
        require(sources, doi, "localized source audit")
    require(sources, "LuoExplicitCutoffTarget", "Luo target")
    require(sources, "preferredFirstLocalizedTargetIsLuoExplicitCutoff", "route order")
    require(sources, "DissipationWavenumberInterface", "dissipation-range interface")
    require(sources, "sequenceDerivedFromDissipationRange", "Cheskidov-Dai semantics")
    require(sources, "mhdToNavierStokesSpecializationOrPeriodicReproof", "MHD specialization")

    print("[2/10] Checking exact periodic LP/Bony construction...")
    periodic = text["periodic_lp"]
    for symbol in (
        "PeriodicHardShellFourierPDE",
        "shellProjector",
        "lowProjector",
        "shellProjectorCommutesWithDerivative",
        "shellProjectorCommutesWithCurl",
        "lowProjectorCommutesWithDerivative",
        "lowProjectorCommutesWithCurl",
        "ownedShellReconstructsMode",
        "ownedLowPassReconstructsMode",
        "PeriodicTriadInteraction",
        "decomposeInteraction",
        "eraseDecomposedInteractions",
        "periodicHardShellProjectorConstructed = true",
        "periodicHardLowPassProjectorConstructed = true",
        "ownedLowPassPointwiseReconstructionClosed = true",
        "bonyTaoInteractionClassificationClosed = true",
        "finiteInteractionRecompositionClosed = true",
    ):
        require(periodic, symbol, "periodic LP/Bony exact")
    require(periodic, "smoothProjectorNormComparisonClosed = false", "smooth comparison gate")
    require(periodic, "localizedContinuationNormEstimateClosed = false", "continuation norm gate")

    print("[3/10] Checking cutoff-indexed profile-depth replacement...")
    depth = text["depth_exact"]
    for symbol in (
        "ProfileDepthEntry",
        "entryDepth N forcedTailEntry = zero",
        "entryDepth N adversarialEntry = N",
        "entryDepth N transitionEntry = N",
        "pow2DominatesSuccessor",
        "ftAdvWeightOrientation",
        "ftTransWeightOrientation",
        "cutoffIndexedProfileDepthGeometryConstructed = true",
        "legacyGlobalDepthPostulatesNeededByThisRoute = false",
    ):
        require(depth, symbol, "cutoff-indexed depth")
    require(depth, "legacyNatEntryIdentificationClosed = false", "legacy index seam")
    require(text["legacy_depth"], "postulate\n  entryDepth", "quarantined legacy depth")

    print("[4/10] Checking exact finite residue/operator/gap authority...")
    residue = text["residue_exact"]
    for symbol in (
        "ExactResidueScaleOperatorGapAuthority",
        "actualQuadraticFormIsError",
        "operatorStrongErrorN2Proof",
        "baseGapN2Proof",
        "operatorErrorN2Proof",
        "gapAbsorptionProof",
        "residueScaleCompatibility",
        "residueScaleCompatibilityRouteClosed",
        "finiteCanonicalOperatorGapAuthorityConstructed = true",
        "strictPositiveGapMarginConstructed = true",
        "residueScaleCompatibilityConstructed = true",
    ):
        require(residue, symbol, "residue/operator/gap exact")
    require(residue, "physicalPairIncidenceKernelIdentificationClosed = false", "physical operator seam")

    print("[5/10] Checking Luo explicit-cutoff control theorem...")
    luo = text["luo"]
    for symbol in (
        "10.1007/s00021-019-0411-z",
        "parabolicWindowDenominator",
        "CutoffForcedTailLocalizedOutput",
        "forcedTailIntegralBound",
        "LuoCutoffLocalizedMajorant",
        "periodicHardShellProjectorConstructed ≡ true",
        "luoLocalizedQuantityBelowThreshold",
        "majorantToLuoExplicitCutoffCriterion",
        "forcedTailOutputControlsLuoCutoffQuantity = true",
    ):
        require(luo, symbol, "Luo exact bridge")
    require(luo, "physicalGradientIntegralIdentificationClosed = false", "gradient identification gate")
    require(luo, "luoLimsupContinuationAuthorityClosed = false", "Luo continuation gate")

    print("[6/10] Checking inventory and generic low/high assembly...")
    inventory = text["inventory"]
    require(inventory, "NSTriadKNPeriodicLittlewoodPaleyBonyExact", "LP inventory")
    require(inventory, "exactPeriodicHardLowPassProjectorConstructed", "low-pass inventory")
    require(inventory, "ownedLowPassPointwiseReconstructionClosed", "low-pass reconstruction inventory")
    require(inventory, "exactPeriodicLPBonyPDEInterfaceConstructed = true", "LP construction receipt")
    require(inventory, "fullLocalizedContinuationProjectorInterfaceClosed = false", "LP analytic gate")
    assembly = text["assembly"]
    for symbol in ("allShellControl", "allShellControlAtTime", "allShellNatBound"):
        require(assembly, symbol, "low/high assembly")
    require(assembly, "finiteLowUniformHighAssemblyClosed = true", "assembly receipt")

    print("[7/10] Checking constructed finite compatibility bridge...")
    compatibility = text["compatibility"]
    require(compatibility, "ExactFiniteBlockersToLuoBridge", "finite bridge type")
    require(compatibility, "exactFiniteBlockersToLuoBridge", "finite bridge inhabitant")
    require(compatibility, "exactFiniteBlockersToLuoBridgeConstructed = true", "finite bridge receipt")
    require(compatibility, "forcedTailBlockerSemanticKind = weightedSchurRestrictedRow", "forced-tail semantics")
    require(compatibility, "residueScaleBlockerSemanticKind = weakStrongQuadraticGapCompatibility", "residue semantics")
    require(compatibility, "finiteBonyPiecesEqualPhysicalNonlinearPieces = false", "physical Bony seam")
    require(compatibility, "blockersToLocalizedBKMBridgeClosed = false", "physical compatibility gate")

    print("[8/10] Checking finite authority versus physical authority...")
    require(text["weight_bridge"], "blocker1DepthRouteClosed = true", "legacy assembled route")
    authority = text["authority"]
    for symbol in (
        "ExactAnalyticBlockerAuthority",
        "exactAnalyticBlockerAuthority",
        "blocker1CutoffIndexedDepthGeometryConstructed",
        "blocker1BothWeightOrientationsConstructed = true",
        "blocker2FiniteCanonicalOperatorGapAuthorityConstructed",
        "blocker2ResidueScaleCompatibilityConstructed",
        "bothFiniteAnalyticCoresConstructed = true",
        "analyticBlockerAuthorityBoundaryAudited = true",
    ):
        require(authority, symbol, "analytic authority")
    require(authority, "blocker1LegacyNatEntryIdentificationClosed", "legacy index seam")
    require(authority, "blocker1PhysicalAuthorityClosed = false", "Blocker 1 physical gate")
    require(authority, "blocker2PhysicalPairIncidenceKernelIdentificationClosed", "operator seam")
    require(authority, "blocker2PhysicalAuthorityClosed = false", "Blocker 2 physical gate")
    require(authority, "bothPhysicalAnalyticBlockersClosed = false", "combined physical gate")

    print("[9/10] Checking integration receipt and original promotion gates...")
    integration = text["integration"]
    for symbol in (
        "exactPeriodicLPBonyPDEInterfaceConstructed",
        "blocker1CutoffIndexedDepthGeometryConstructed",
        "blocker1BothWeightOrientationsConstructed",
        "blocker2FiniteCanonicalOperatorGapAuthorityConstructed",
        "blocker2ResidueScaleCompatibilityConstructed",
        "forcedTailOutputControlsLuoCutoffQuantity",
        "localizedBKMConstructionTrancheComplete = true",
    ):
        require(integration, symbol, "integration receipt")
    require(integration, "physicalGradientIntegralIdentificationClosed", "physical integral seam")
    require(integration, "luoLimsupContinuationAuthorityClosed", "continuation seam")
    require(integration, "existingBKMExclusionStillFalse", "BKM gate")
    require(integration, "existingClayPromotionStillFalse", "Clay gate")
    require(integration, "localizedBKMRouteReadyForPromotion = false", "promotion gate")
    require(text["pair_bounds"], "canonicalBKMExclusionProved = false", "legacy BKM gate")

    print("[10/10] Rejecting new axioms and accidental promotions...")
    for name in NEW_AXIOM_FREE_FILES:
        forbid(text[name], "\npostulate\n", name)
        forbid(text[name], "\npostulate ", name)
        forbid(text[name], "bkmExclusionProved = true", name)
        forbid(text[name], "clayNavierStokesPromoted = true", name)
        forbid(text[name], "localizedBKMRouteReadyForPromotion = true", name)

    print("PASS: exact localized-BKM finite construction is attributed and fail-closed at the physical seam.")
    print("NOTE: run focused Track B Agda checks separately; this script is a static audit only.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
