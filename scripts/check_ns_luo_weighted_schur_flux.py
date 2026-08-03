#!/usr/bin/env python3
"""Fail-closed static audit for the official Luo continuation tranche."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLOSURE = ROOT / "DASHI" / "Physics" / "Closure"

FILES = {
    "source": CLOSURE / "NSTriadKNLuoPrimarySourceProofArchitectureExact.agda",
    "hard_selection": CLOSURE / "NSTriadKNPhysicalHardHighTriadSelectionExact.agda",
    "finite_hermitian": CLOSURE / "NSTriadKNFiniteHermitianDiagonalMultiplierExact.agda",
    "coefficient_projector": CLOSURE / "NSTriadKNHardProjectorCoefficientSelfAdjointExact.agda",
    "parseval_surface": CLOSURE / "NSTriadKNHardProjectorParsevalTransportExact.agda",
    "official_parseval": CLOSURE / "NSTriadKNOfficialFiniteFourierHermitianParsevalExact.agda",
    "radial_surface": CLOSURE / "NSTriadKNLuoRadialSmoothMultiplierExact.agda",
    "multiplier_surface": CLOSURE / "NSTriadKNLuoPeriodicMultiplierKernelBoundExact.agda",
    "concrete_multiplier": CLOSURE / "NSTriadKNLuoConcreteRadialMultiplierKernelExact.agda",
    "z3_encoding": CLOSURE / "NSTriadKNHardHighPhysicalZ3PairEncodingExact.agda",
    "cross_carrier": CLOSURE / "NSTriadKNLuoCrossCarrierRationalIdentificationExact.agda",
    "leray_hopf": CLOSURE / "NSTriadKNRegularLerayHopfPeriodicSolutionExact.agda",
    "official_energy": CLOSURE / "NSTriadKNLuoOfficialPhysicalEnergyTimeExact.agda",
    "published_luo": CLOSURE / "NSTriadKNLuoPublishedContinuationAuthorityExact.agda",
    "official_authority": CLOSURE / "NSTriadKNLuoOfficialLerayHopfAuthorityExact.agda",
    "official_closure": CLOSURE / "NSTriadKNLuoOfficialContinuationClosureExact.agda",
    "official_receipt": CLOSURE / "NSTriadKNLuoOfficialContinuationIntegration.agda",
    "pair_bounds": CLOSURE / "NSTriadKNPairIncidenceProfileBounds.agda",
    "dictionary": ROOT / "docs" / "ns-localized-bkm-variable-dictionary.md",
}


def fail(message: str) -> None:
    print(f"FAIL: {message}")
    raise SystemExit(1)


def load() -> dict[str, str]:
    loaded: dict[str, str] = {}
    for name, path in FILES.items():
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        loaded[name] = path.read_text(encoding="utf-8")
    return loaded


def require_all(text: str, needles: tuple[str, ...], label: str) -> None:
    for needle in needles:
        if needle not in text:
            fail(f"{label}: missing {needle!r}")


def forbid(text: str, needle: str, label: str) -> None:
    if needle in text:
        fail(f"{label}: forbidden {needle!r}")


def main() -> int:
    t = load()

    print("[1/9] Luo source and hard-high finite infrastructure")
    require_all(t["source"], (
        "10.1007/s00021-019-0411-z",
        "fullLowPassGradientInfinityIntegral",
        "viscosityNormalizedToOne",
        "fluxBoundByEnergyMajorantTimesLowPassGradient",
    ), "Luo source")
    require_all(t["hard_selection"], (
        "hardHighPhysicalTriadSelectionSound",
        "hardHighPhysicalTriadSelectionComplete",
        "hardHighPhysicalTriadNoDuplicates",
    ), "hard-high selection")

    print("[2/9] Official finite Hermitian Parseval")
    require_all(t["finite_hermitian"], (
        "finiteDiagonalMultiplierSelfAdjoint",
        "finiteHermitianDiagonalSelfAdjointnessConstructed = true",
    ), "finite Hermitian theorem")
    require_all(t["coefficient_projector"], (
        "hardLowCoefficientSelfAdjoint",
        "hardHighCoefficientSelfAdjoint",
        "hardProjectorCoefficientSelfAdjointnessClosed = true",
    ), "coefficient projector")
    require_all(t["parseval_surface"], (
        "PeriodicHermitianParsevalTransport",
        "HardProjectorOrthogonalCertificate",
        "officialPhysicalHermitianParsevalTransportSelected = false",
    ), "generic Parseval surface")
    require_all(t["official_parseval"], (
        "officialFiniteHermitianPairing",
        "officialFinitePairingIsCoefficientPairing",
        "officialFiniteHermitianParsevalTransport",
        "officialHardProjectorOrthogonal",
        "officialCoefficientUnitaryGlobalParseval",
        "officialCoefficientUnitaryShellParseval",
        "officialFiniteFourierHermitianParsevalLevel = machineChecked",
        "officialFiniteFourierPairingSelected = true",
    ), "official finite Parseval selection")

    print("[3/9] Concrete Luo radial multiplier and periodic kernel")
    require_all(t["radial_surface"], (
        "symbolIsOneOnInnerThreeQuarterBall",
        "symbolVanishesOutsideUnitBall",
        "smoothLowPassFactorsThroughHardNext",
    ), "radial support surface")
    require_all(t["multiplier_surface"], (
        "PublishedLuoPeriodicMultiplierKernelAuthority",
        "luoSmoothCriterionFromHardBudget",
    ), "multiplier authority surface")
    require_all(t["concrete_multiplier"], (
        "normalizedExponentialThreeQuarterToOne",
        "PeriodizedDyadicKernelL1Theorem",
        "periodizedKernelL1BoundUniformInShell",
        "canonicalLuoMultiplierAuthority",
        "canonicalLuoRadialCutoffSelectionLevel = standardImported",
        "canonicalPeriodizedKernelL1TheoremLevel = standardImported",
        "cutoffUniformPeriodicKernelL1BoundSelected = true",
    ), "concrete multiplier selection")

    print("[4/9] Exact physical triad to Z3 full-shell pair encoding")
    require_all(t["z3_encoding"], (
        "encodePhysicalPair",
        "encodedPhysicalPairResonates",
        "decodeEncodedPhysicalPair",
        "encodeDecodedResonantPair",
        "hardHighPhysicalZ3Pairs",
        "HardHighPhysicalZ3FullShellPairIdentification",
        "encodedHardHighListIsFullShellPairList",
        "hardHighPhysicalToZ3PairEncodingClosed = true",
    ), "Z3 pair encoding")

    print("[5/9] Four cross-carrier equalities")
    require_all(t["cross_carrier"], (
        "RationalizedFullShellPhysicalBridgeInputs",
        "transportedMajorantSchurBound",
        "physicalBridgeFromFullShell",
        "fullShellFluxMatchesPhysicalBridge",
        "fullShellSchurConstantMatchesPhysicalBridge",
        "fullShellEnergyMatchesPhysicalBridge",
        "fullShellGradientMatchesPhysicalBridge",
        "fourCrossCarrierEqualitiesClosed = true",
    ), "cross-carrier rational owner")

    print("[6/9] Regular Leray-Hopf and physical energy/time identities")
    require_all(t["leray_hopf"], (
        "PeriodicLerayHopfSolution",
        "RegularLerayHopfBeforeTerminal",
        "globalLerayHopfEnergyInequality",
        "two * integratedGradientL2SquaredFromZero",
        "OfficialLuoCutoffQuantities",
        "physicalDissipationMeaning",
        "preterminalProjectedEnergyIdentity",
        "IntegratedFluxIsTimeIntegralOfPointwiseFlux",
        "factorTwoDissipationNormalizationRecorded = true",
        "preterminalEnergyIdentitySeparatedFromWeakInequality = true",
    ), "regular Leray-Hopf carrier")
    require_all(t["official_energy"], (
        "OfficialLuoPhysicalEnergyTimeIdentification",
        "officialHardProjectorOrthogonal",
        "pointwiseProjectedFluxMeaning",
        "officialCurrentEnergyMeaning",
        "officialDissipationMeaning",
        "officialIntegratedFluxMeaning",
        "officialWeightedEnergyMeaning",
        "officialLocalizedGradientMeaning",
        "officialPhysicalEnergyRecursion",
        "officialPhysicalEnergyTimeCarrierSelected = true",
    ), "official energy/time owner")

    print("[7/9] Luo authority selected on exact source carrier")
    require_all(t["published_luo"], (
        "PublishedLuoTheorem11Authority",
        "pointwiseThresholdImpliesLimsupBound",
        "luoTheorem11AuthorityLevel = standardImported",
    ), "published Luo theorem")
    require_all(t["official_authority"], (
        "OfficialPeriodicLuoSourceCarrier",
        "lerayHopfInitialMeaning",
        "lerayHopfSolutionMeaning",
        "PeriodicDomainIsThreeTorus",
        "ViscosityIsExactlyOne",
        "SourceNormalizationMatchesLuo",
        "officialPeriodicLuoAuthority",
        "selectedLuoAuthorityLevel = standardImported",
        "officialPeriodicLuoCarrierSelected = true",
    ), "official Luo authority")

    print("[8/9] Full official continuation composition")
    require_all(t["official_closure"], (
        "OfficialLuoContinuationClosure",
        "officialHardHighListMatchesFullShell",
        "officialFluxCrossCarrierEquality",
        "officialSchurCrossCarrierEquality",
        "officialEnergyCrossCarrierEquality",
        "officialGradientCrossCarrierEquality",
        "officialSmoothCutoffBound",
        "officialSourceCutoffBound",
        "officialSourceLimsupBound",
        "officialLuoContinuation",
        "allSixOfficialIdentificationTasksComposed = true",
        "localizedRoutePromotedToClay = false",
    ), "official continuation closure")
    require_all(t["official_receipt"], (
        "OfficialLuoContinuationIntegrationReceipt",
        "officialLuoIdentificationTrancheComplete = true",
        "officialLuoRouteReadyForClayPromotion = false",
        "BKMExclusionStillFalse",
        "ClayPromotionStillFalse",
    ), "official completion receipt")

    print("[9/9] Rejecting axioms and accidental promotion")
    for name, content in t.items():
        if name in {"pair_bounds", "dictionary"}:
            continue
        forbid(content, "\npostulate\n", name)
        forbid(content, "\npostulate ", name)
        forbid(content, "canonicalBKMExclusionProved = true", name)
        forbid(content, "clayNavierStokesPromoted = true", name)
        forbid(content, "localizedRoutePromotedToClay = true", name)
    require_all(t["pair_bounds"], (
        "canonicalBKMExclusionProved = false",
    ), "legacy BKM gate")
    require_all(t["dictionary"], (
        "Weighted Schur is used on the flux/energy factor",
    ), "variable dictionary")

    print("PASS: all six official Luo identification tasks are represented, attributed, and fail-closed against Clay promotion.")
    print("NOTE: standard-imported multiplier/Luo theorems remain non-promotable; run the focused Agda checker separately.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
