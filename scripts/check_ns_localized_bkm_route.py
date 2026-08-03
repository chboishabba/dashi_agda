#!/usr/bin/env python3
"""Fail-closed static audit for the localized BKM reconnaissance tranche.

This checker verifies source attribution, existing LP/Bony reuse, constructive
low/high assembly, explicit semantic and authority boundaries for the live
blockers, and preservation of all BKM/Clay fail-closed gates.  It is not an
Agda typecheck.
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
    "compatibility": CLOSURE / "NSTriadKNBlockerToLocalizedBKMCompatibility.agda",
    "authority": CLOSURE / "NSTriadKNAnalyticBlockerAuthorityAudit.agda",
    "integration": CLOSURE / "NSTriadKNLocalizedBKMRouteIntegration.agda",
    "forced_tail": CLOSURE / "NSTriadKNProfileCrossForcedTailRefinement.agda",
    "depth_base": CLOSURE / "NSTriadKNProfileDepthGeometryBase.agda",
    "weight_bridge": CLOSURE / "NSTriadKNProfileCrossWeightBridge.agda",
    "pair_bounds": CLOSURE / "NSTriadKNPairIncidenceProfileBounds.agda",
}


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

    print("[1/8] Checking primary-source provenance and route semantics...")
    sources = text["sources"]
    for doi in (
        "10.1007/BF01212349",
        "10.1007/s00021-014-0167-4",
        "10.1017/S0013091525100813",
        "10.1007/s00220-007-0319-y",
    ):
        require(sources, doi, "localized source audit")
    require(sources, "DissipationWavenumberInterface", "dissipation-range interface")
    require(sources, "sourceDefinedTerminalSequenceTq", "Cheskidov-Dai scope")
    require(sources, "sequenceDerivedFromDissipationRange", "Cheskidov-Dai sequence semantics")
    require(sources, "mhdToNavierStokesSpecializationOrPeriodicReproof", "Chen-Miao-Zhang scope")

    print("[2/8] Checking reuse and limits of existing LP/Bony infrastructure...")
    inventory = text["inventory"]
    for module in (
        "NSTriadKNExactDyadicShellGeometry",
        "NSTriadKNHardDyadicShellOwner",
        "NSTriadKNRationalFiniteBernstein",
        "NSTriadKNTaoFrozenLegParaproductProgram",
        "NSTriadKNOutputRelocationKatoPonceBonyScopeAudit",
        "NSTriadKNDongLiFrequencyLocalizedCoercivityAudit",
    ):
        require(inventory, module, "LP inventory")
    require(inventory, "LiteralNavierStokesBonyDecomposition", "literal Bony target")
    require(inventory, "literalNavierStokesBonyDecompositionClosed = false", "Bony inventory gate")
    require(inventory, "fullLocalizedContinuationProjectorInterfaceClosed = false", "LP inventory gate")

    print("[3/8] Checking constructive low/high assembly...")
    assembly = text["assembly"]
    require(assembly, "allShellControl", "fixed-cutoff assembly")
    require(assembly, "allShellControlAtTime", "time-dependent assembly")
    require(assembly, "allShellNatBound", "quantitative assembly")
    require(assembly, "finiteLowUniformHighAssemblyClosed = true", "assembly receipt")

    print("[4/8] Checking blocker semantics and explicit adapters...")
    compatibility = text["compatibility"]
    require(compatibility, "forcedTailBlockerSemanticKind = weightedSchurRestrictedRow", "forced-tail semantics")
    require(compatibility, "residueScaleBlockerSemanticKind = weakStrongQuadraticGapCompatibility", "residue semantics")
    require(compatibility, "ForcedTailToLocalizedVorticityBridge", "forced-tail adapter")
    require(compatibility, "literalNavierStokesBonyDecomposition", "Bony adapter")
    require(compatibility, "ResidueScaleToDissipationWavenumberBridge", "residue-scale adapter")
    require(compatibility, "dissipationRange", "Q(t) adapter")
    require(compatibility, "forcedTailResidualsIdentifiedWithBonyPieces = false", "Bony identification gate")
    require(compatibility, "blockersToLocalizedBKMBridgeClosed = false", "compatibility gate")

    print("[5/8] Checking theorem-shape versus constructive authority...")
    require(text["weight_bridge"], "blocker1DepthRouteClosed = true", "assembled Blocker 1 route")
    require(text["depth_base"], "postulate\n  entryDepth", "Blocker 1 depth authority")
    authority = text["authority"]
    require(authority, "ConstructiveProfileDepthGeometry", "Blocker 1 replacement target")
    require(authority, "CurrentDepthBaseRealization", "Blocker 1 realization target")
    require(authority, "ConstructiveResidueScaleCompatibilityAuthority", "Blocker 2 authority target")
    require(authority, "blocker1RestrictedRowRouteAssembled =", "Blocker 1 packaged status")
    require(authority, "blocker1PostulateFreeAuthorityClosed = false", "Blocker 1 authority gate")
    require(authority, "blocker2ResidueScaleCompatibilityConstructed = false", "Blocker 2 authority gate")
    require(authority, "analyticBlockerAuthorityBoundaryAudited = true", "authority audit receipt")

    print("[6/8] Checking that the original blockers remain visible...")
    require(text["forced_tail"], "ForcedTailToAdversarialRestrictedRowN1", "forced-tail blocker")
    require(text["forced_tail"], "ForcedTailToTransitionRestrictedRowN1", "forced-tail blocker")
    require(text["pair_bounds"], "QGap.ResidueScaleCompatibility", "residue-scale blocker")
    require(text["pair_bounds"], "canonicalBKMExclusionProved = false", "BKM gate")

    print("[7/8] Checking fail-closed integration receipt...")
    integration = text["integration"]
    require(integration, "blockerAuthorityBoundaryAudited", "integration receipt")
    require(integration, "blocker1RestrictedRowRouteAssembled", "integration receipt")
    require(integration, "blocker1PostulateFreeAuthorityClosed", "integration receipt")
    require(integration, "blocker2ResidueScaleCompatibilityConstructed", "integration receipt")
    require(integration, "literalNavierStokesBonyDecompositionClosed", "integration receipt")
    require(integration, "forcedTailResidualsIdentifiedWithBonyPieces", "integration receipt")
    require(integration, "existingBKMExclusionStillFalse", "integration receipt")
    require(integration, "existingClayPromotionStillFalse", "integration receipt")
    require(integration, "localizedBKMRouteReadyForPromotion = false", "integration gate")
    require(integration, "localizedBKMReconnaissanceComplete = true", "reconnaissance receipt")

    print("[8/8] Rejecting declarations of new axioms and accidental promotions...")
    for name in ("inventory", "sources", "assembly", "compatibility", "authority", "integration"):
        forbid(text[name], "\npostulate\n", name)
        forbid(text[name], "\npostulate ", name)
        forbid(text[name], "bkmExclusionProved = true", name)
        forbid(text[name], "clayNavierStokesPromoted = true", name)
        forbid(text[name], "localizedBKMRouteReadyForPromotion = true", name)

    print("PASS: localized BKM reconnaissance is attributed, constructive where claimed, and fail-closed.")
    print("NOTE: run Track B Agda checks separately; this script is a static audit only.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
