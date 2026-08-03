#!/usr/bin/env python3
"""Fail-closed static audit for the Luo weighted-Schur cutoff-flux tranche."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLOSURE = ROOT / "DASHI" / "Physics" / "Closure"

FILES = {
    "scale": CLOSURE / "NSTriadKNLocalizedBKMScaleDictionaryExact.agda",
    "source": CLOSURE / "NSTriadKNLuoPrimarySourceProofArchitectureExact.agda",
    "enumeration": CLOSURE / "NSTriadKNProjectedConvolutionIncidenceEnumerationExact.agda",
    "physical_reuse": CLOSURE / "NSTriadKNLuoPhysicalEnumerationReuseExact.agda",
    "hard_selection": CLOSURE / "NSTriadKNPhysicalHardHighTriadSelectionExact.agda",
    "hard_projector": CLOSURE / "NSTriadKNPeriodicHardProjectorAlgebraExact.agda",
    "hard_smooth": CLOSURE / "NSTriadKNHardSmoothLittlewoodPaleyTransferExact.agda",
    "flux": CLOSURE / "NSTriadKNPhysicalCutoffFluxWeightedSchurExact.agda",
    "reuse": CLOSURE / "NSTriadKNWeightedSchurPhysicalFluxReuseExact.agda",
    "full_shell": CLOSURE / "NSTriadKNLuoFullShellFluxAdapterExact.agda",
    "energy": CLOSURE / "NSTriadKNProjectedConvectionEnergyFluxExact.agda",
    "bootstrap": CLOSURE / "NSTriadKNLuoCutoffEnergyBootstrapExact.agda",
    "integration": CLOSURE / "NSTriadKNLuoWeightedSchurFluxIntegration.agda",
    "top": CLOSURE / "NSTriadKNLocalizedBKMRouteIntegration.agda",
    "weighted_schur": CLOSURE / "NSTriadKNWeightedSchurProductBound.agda",
    "physical_triads": CLOSURE / "NSTriadKNPhysicalTriadEnumeration.agda",
    "physical_fibre": CLOSURE / "NSTriadKNValidatedPhysicalFiberImage.agda",
    "full_shell_existing": CLOSURE / "NSCompactGammaFullShellSchur.agda",
    "pair_bounds": CLOSURE / "NSTriadKNPairIncidenceProfileBounds.agda",
    "dictionary": ROOT / "docs" / "ns-localized-bkm-variable-dictionary.md",
}

NEW_AGDA = (
    "scale",
    "source",
    "enumeration",
    "physical_reuse",
    "hard_selection",
    "hard_projector",
    "hard_smooth",
    "flux",
    "reuse",
    "full_shell",
    "energy",
    "bootstrap",
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


def load() -> dict[str, str]:
    loaded: dict[str, str] = {}
    for name, path in FILES.items():
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        loaded[name] = path.read_text(encoding="utf-8")
    return loaded


def require_all(text: str, needles: tuple[str, ...], label: str) -> None:
    for needle in needles:
        require(text, needle, label)


def main() -> int:
    text = load()

    print("[1/10] Luo source and scale fidelity")
    require_all(text["source"], (
        "10.1007/s00021-019-0411-z",
        "fullLowPassGradientInfinityIntegral",
        "viscosityNormalizedToOne",
        "LuoProposition31FluxTarget",
        "fluxBoundByEnergyMajorantTimesLowPassGradient",
        "LuoSmallTimeEnergyDissipationTarget",
    ), "Luo source architecture")
    require_all(text["scale"], (
        "shellIndexRole", "dyadicWavenumberRole",
        "parabolicDenominatorRole", "finiteModeCountRole",
        "profileDepthRole", "galerkinCutoffRole",
        "localizedBKMScaleRolesSeparated = true",
    ), "scale dictionary")
    require(text["dictionary"], "Weighted Schur is used on the flux/energy factor", "markdown dictionary")

    print("[2/10] Exact physical enumeration and hard selection")
    require_all(text["physical_reuse"], (
        "physicalTriadEnumerationImplementedIsTrue",
        "physicalTriadEnumerationDuplicateFreeIsTrue",
        "physicalOutputFiberImplementedIsTrue",
        "hardProjectedHighFrequencySelectionConstructed = true",
        "validatedPhysicalFiberImageConstructedIsTrue",
        "exactPhysicalKernelIdentificationReductionImplementedIsTrue",
    ), "physical enumeration reuse")
    require_all(text["hard_selection"], (
        "hardHighPhysicalTriads",
        "filterHighSound", "filterHighComplete", "filterHighNoDuplicates",
        "hardHighPhysicalTriadSelectionSound",
        "hardHighPhysicalTriadSelectionComplete",
        "hardHighPhysicalTriadNoDuplicates",
        "hardHighOutputSelectionConstructed = true",
        "hardLowHighPartitionConstructed = true",
    ), "hard high selector")
    require(text["physical_triads"], "physicalTriadEnumerationImplemented = true", "literal physical triads")
    require(text["physical_fibre"], "validatedPhysicalFiberImageConstructed = true", "physical fibre")

    print("[3/10] Pair-incidence multiplicity and Hermitian majorants")
    require_all(text["enumeration"], (
        "ExactFiniteEnumeration", "NoDuplicates", "PairIncidenceSlot",
        "triadContributesExactlyThreeIncidences",
        "PhysicalFibreMultiplicityAgreement", "fibreLengthsAgree",
    ), "enumeration interface")
    require_all(text["flux"], (
        "complexDifferenceNormSquared", "HermitianPairIncidenceAtom",
        "physicalTriadTermDominatedByIncidenceMajorant",
        "fiberMultiplicityMatchesConvolutionMultiplicity",
        "physicalMajorantEqualsProfileSum",
        "physicalCutoffFluxDominatedByPairIncidenceFold",
        "physicalCutoffFluxDominatedByWeightedSchurMajorant",
        "luoCutoffFluxEstimate",
        "physicalWeightedSchurBridgeInhabited = false",
    ), "Hermitian flux theorem")

    print("[4/10] Hard projector and hard/smooth transfer")
    require_all(text["hard_projector"], (
        "lowProjectorIdempotent", "highProjectorIdempotent",
        "lowAfterHighIsZero", "highAfterLowIsZero",
        "highProjectorCommutesWithDerivative",
        "highProjectorCommutesWithCurl",
        "hardLowHighDisjointnessConstructed = true",
        "hardProjectorHermitianL2SelfAdjointnessClosed = false",
    ), "hard projector algebra")
    require_all(text["hard_smooth"], (
        "HardBandWitness", "smoothSupportOccursInHardBand",
        "HardSmoothTerminalWindowComparison",
        "hardTerminalWindowBudgetTransfersToLuoSmoothCriterion",
        "hardSmoothTerminalWindowTransferConstructed = true",
        "concreteSmoothPeriodicMultiplierFamilyConstructed = false",
        "uniformHardSmoothFiniteBandConstantConstructed = false",
    ), "hard-smooth transfer")

    print("[5/10] Existing weighted-Schur and full-shell reuse")
    require_all(text["reuse"], (
        "weightedSchurProductBoundClosed ≡ true",
        "weightedSchurMatrixOperatorDataClosed ≡ false",
        "weightedSchurRelevantToLuoFluxRoute = true",
    ), "weighted-Schur reuse")
    require(text["weighted_schur"], "weightedSchurProductBoundClosed = true", "existing Schur algebra")
    require_all(text["full_shell"], (
        "Closure.closureNearResponseMajorized",
        "luoFullShellCutoffFluxEstimate",
        "matureFullShellNearMajorizationReused = true",
        "matureFullShellUniformSchurReused = true",
        "luoFullShellPhysicalIdentificationInhabited = false",
    ), "full-shell Luo adapter")
    require_all(text["full_shell_existing"], (
        "everyLocalFourierMajorization", "certificateAt",
    ), "existing full shell")

    print("[6/10] Projected energy-flux composition")
    require_all(text["energy"], (
        "ProjectedCutoffEnergyBalance",
        "divergenceFreePressureCancellation",
        "highFrequencyEnergyInequality",
        "PeriodicProjectedConvectionFluxAdapter",
        "HardHighPassProjectorSelfAdjoint",
        "hardHighPassProjectorSelfAdjoint",
        "projectedEnergyControlledByWeightedSchurFlux",
        "periodicProjectedConvectionFluxAdapterInhabited = false",
    ), "projected energy flux")

    print("[7/10] Luo cutoff bootstrap")
    require_all(text["bootstrap"], (
        "LuoParabolicTimeCutoff",
        "SupportInShiftedParabolicWindow",
        "supportInShiftedParabolicWindow",
        "LuoCutoffEnergyFluxData",
        "localizedGradientSubstitution",
        "luoSmallTimeEnergyDissipationRecursion",
        "LuoCutoffBootstrapCertificate",
        "luoCutoffBootstrapBound",
        "BootstrapDecayImpliesRegularity",
        "bootstrapDecayImpliesRegularity",
        "physicalLuoBootstrapAdapterInhabited = false",
    ), "Luo bootstrap")

    print("[8/10] Consolidated fail-closed ledger")
    require_all(text["integration"], (
        "literalPhysicalCutoffEnumerationAvailable",
        "hardProjectedHighFrequencySelectionConstructed",
        "hardLowProjectorIdempotenceConstructed",
        "matureFullShellNearMajorizationReused",
        "hardSmoothTransferAlgebraConstructed",
        "luoWeightedSchurFluxTrancheComplete = true",
        "concreteSmoothPeriodicMultiplierOpen",
        "physicalTriadCoefficientDominationOpen",
        "fullShellPhysicalIdentificationOpen",
        "periodicHighPassSelfAdjointnessOpen",
        "luoWeightedSchurFluxRouteReadyForPromotion = false",
        "existingBKMExclusionStillFalse",
        "existingClayPromotionStillFalse",
    ), "flux integration")
    require(text["top"], "weightedSchurFluxTrancheConstructed", "top integration")
    require(text["pair_bounds"], "canonicalBKMExclusionProved = false", "legacy BKM gate")

    print("[9/10] Proof-relevant semantic boundaries")
    for label, content, pairs in (
        ("energy adapter", text["energy"], (
            ("HardHighPassProjectorSelfAdjoint", "hardHighPassProjectorSelfAdjoint"),
            ("ProjectedConvectionTriadsExactlyEnumerated", "projectedConvectionTriadsExactlyEnumerated"),
        )),
        ("bootstrap adapter", text["bootstrap"], (
            ("PhysicalEnergyIdentityMatchesCutoffData", "physicalEnergyIdentityMatchesCutoffData"),
            ("BootstrapDecayImpliesRegularity", "bootstrapDecayImpliesRegularity"),
        )),
        ("full-shell adapter", text["full_shell"], (
            ("SelectedPairListIsHardHighPhysicalTriadImage", "selectedPairListIsHardHighPhysicalTriadImage"),
            ("ProfileSchurConstantUniformInCutoff", "profileSchurConstantUniformInCutoff"),
        )),
    ):
        for proposition, witness in pairs:
            require(content, proposition, label)
            require(content, witness, label)

    print("[10/10] Rejecting new axioms and accidental promotion")
    for name in NEW_AGDA:
        forbid(text[name], "\npostulate\n", name)
        forbid(text[name], "\npostulate ", name)
        forbid(text[name], "bkmExclusionProved = true", name)
        forbid(text[name], "clayNavierStokesPromoted = true", name)
        forbid(text[name], "RouteReadyForPromotion = true", name)

    print("PASS: Luo weighted-Schur flux tranche is attributed and fail-closed at the exact remaining physical seam.")
    print("NOTE: this is a static source audit; run the focused Agda checker separately.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
