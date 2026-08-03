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
    result: dict[str, str] = {}
    for name, path in FILES.items():
        if not path.is_file():
            fail(f"missing {path.relative_to(ROOT)}")
        result[name] = path.read_text(encoding="utf-8")
    return result


def main() -> int:
    text = load()

    print("[1/13] Checking Luo source fidelity...")
    source = text["source"]
    for token in (
        "10.1007/s00021-019-0411-z",
        "LuoTheorem11Target",
        "fullLowPassGradientInfinityIntegral",
        "viscosityNormalizedToOne",
        "LuoProposition31FluxTarget",
        "fluxBoundByEnergyMajorantTimesLowPassGradient",
        "LuoSmallTimeEnergyDissipationTarget",
    ):
        require(source, token, "Luo source architecture")

    print("[2/13] Checking scale-role separation...")
    scale = text["scale"]
    for token in (
        "shellIndexRole",
        "dyadicWavenumberRole",
        "parabolicDenominatorRole",
        "finiteModeCountRole",
        "profileDepthRole",
        "galerkinCutoffRole",
        "shellWavenumber shell ≡ pow2 shell",
        "localizedBKMScaleRolesSeparated = true",
    ):
        require(scale, token, "scale dictionary")
    dictionary = text["dictionary"]
    require(dictionary, "Never rewrite `(N + 1)^-1`", "markdown dictionary")
    require(dictionary, "Weighted Schur is used on the flux/energy factor", "markdown dictionary")

    print("[3/13] Checking exact physical triad/fibre reuse...")
    physical_reuse = text["physical_reuse"]
    for token in (
        "physicalTriadEnumerationImplementedIsTrue",
        "physicalTriadEnumerationDuplicateFreeIsTrue",
        "physicalOutputFiberImplementedIsTrue",
        "hardProjectedHighFrequencySelectionConstructed = true",
        "validatedPhysicalFiberImageConstructedIsTrue",
        "exactPhysicalKernelIdentificationReductionImplementedIsTrue",
        "hardProjectorComparedWithLuoSmoothProjector = false",
    ):
        require(physical_reuse, token, "physical enumeration reuse")
    require(text["physical_triads"], "physicalTriadEnumerationImplemented = true", "literal physical triads")
    require(text["physical_fibre"], "validatedPhysicalFiberImageConstructed = true", "validated physical fibre")

    print("[4/13] Checking hard projected high-output selection...")
    hard_selection = text["hard_selection"]
    for token in (
        "hardHighPhysicalTriads",
        "filterHighMemberWasOriginal",
        "filterHighSound",
        "filterHighComplete",
        "filterHighNoDuplicates",
        "hardHighPhysicalTriadSelectionSound",
        "hardHighPhysicalTriadSelectionComplete",
        "hardHighPhysicalTriadNoDuplicates",
        "hardHighOutputSelectionConstructed = true",
        "hardLowHighPartitionConstructed = true",
    ):
        require(hard_selection, token, "hard high selector")

    print("[5/13] Checking multiplicity-safe enumeration interfaces...")
    enumeration = text["enumeration"]
    for token in (
        "ExactFiniteEnumeration",
        "NoDuplicates",
        "PairIncidenceSlot",
        "triadContributesExactlyThreeIncidences",
        "PhysicalFibreMultiplicityAgreement",
        "fibreLengthsAgree",
        "physicalProjectedConvolutionTriadEnumerationInhabited = false",
    ):
        require(enumeration, token, "projected enumeration interface")

    print("[6/13] Checking hard projector and hard/smooth transfer algebra...")
    hard_projector = text["hard_projector"]
    for token in (
        "highProjector",
        "lowProjectorIdempotent",
        "highProjectorIdempotent",
        "lowAfterHighIsZero",
        "highAfterLowIsZero",
        "highProjectorCommutesWithDerivative",
        "highProjectorCommutesWithCurl",
        "hardLowHighDisjointnessConstructed = true",
    ):
        require(hard_projector, token, "hard projector algebra")
    hard_smooth = text["hard_smooth"]
    for token in (
        "HardBandWitness",
        "smoothSupportOccursInHardBand",
        "HardSmoothTerminalWindowComparison",
        "hardTerminalWindowBudgetTransfersToLuoSmoothCriterion",
        "hardSmoothTerminalWindowTransferConstructed = true",
        "concreteSmoothPeriodicMultiplierFamilyConstructed = false",
    ):
        require(hard_smooth, token, "hard smooth transfer")

    print("[7/13] Checking Hermitian physical-flux domination...")
    flux = text["flux"]
    for token in (
        "complexDifferenceNormSquared",
        "HermitianPairIncidenceAtom",
        "physicalTriadTermDominatedByIncidenceMajorant",
        "fiberMultiplicityMatchesConvolutionMultiplicity",
        "physicalMajorantEqualsProfileSum",
        "physicalCutoffFluxDominatedByPairIncidenceFold",
        "physicalCutoffFluxDominatedByWeightedSchurMajorant",
        "luoCutoffFluxEstimate",
    ):
        require(flux, token, "physical flux theorem")
    require(flux, "physicalWeightedSchurBridgeInhabited = false", "physical flux gate")

    print("[8/13] Checking existing weighted-Schur and full-shell reuse...")
    reuse = text["reuse"]
    require(reuse, "weightedSchurProductBoundClosed ≡ true", "Schur reuse")
    require(reuse, "weightedSchurMatrixOperatorDataClosed ≡ false", "Schur concrete gate")
    require(reuse, "weightedSchurRelevantToLuoFluxRoute = true", "Schur relevance")
    require(text["weighted_schur"], "weightedSchurProductBoundClosed = true", "existing Schur algebra")
    full_shell = text["full_shell"]
    for token in (
        "Closure.closureNearResponseMajorized",
        "luoFullShellCutoffFluxEstimate",
        "matureFullShellNearMajorizationReused = true",
        "matureFullShellUniformSchurReused = true",
        "luoFullShellPhysicalIdentificationInhabited = false",
    ):
        require(full_shell, token, "full-shell Luo adapter")
    require(text["full_shell_existing"], "everyLocalFourierMajorization", "existing full shell")
    require(text["full_shell_existing"], "certificateAt", "existing full-shell Schur")

    print("[9/13] Checking projected energy-flux composition...")
    energy = text["energy"]
    for token in (
        "ProjectedCutoffEnergyBalance",
        "divergenceFreePressureCancellation",
        "highFrequencyEnergyInequality",
        "PeriodicProjectedConvectionFluxAdapter",
        "HardHighPassProjectorSelfAdjoint",
        "hardHighPassProjectorSelfAdjoint",
        "projectedEnergyControlledByWeightedSchurFlux",
    ):
        require(energy, token, "projected energy flux")
    require(energy, "periodicProjectedConvectionFluxAdapterInhabited = false", "projected physical gate")

    print("[10/13] Checking Luo bootstrap algebra...")
    bootstrap = text["bootstrap"]
    for token in (
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
    ):
        require(bootstrap, token, "Luo bootstrap")
    require(bootstrap, "physicalLuoBootstrapAdapterInhabited = false", "bootstrap physical gate")

    print("[11/13] Checking integrated fail-closed ledger...")
    integration = text["integration"]
    for token in (
        "literalPhysicalCutoffEnumerationAvailable",
        "hardProjectedHighFrequencySelectionConstructed",
        "validatedPhysicalKernelImageAvailable",
        "luoWeightedSchurFluxTrancheComplete = true",
        "hardSmoothProjectorComparisonOpen",
        "physicalTriadCoefficientDominationOpen",
        "luoWeightedSchurFluxRouteReadyForPromotion = false",
        "existingBKMExclusionStillFalse",
        "existingClayPromotionStillFalse",
    ):
        require(integration, token, "flux integration")
    require(text["top"], "weightedSchurFluxTrancheConstructed", "top integration")
    require(text["pair_bounds"], "canonicalBKMExclusionProved = false", "legacy BKM gate")

    print("[12/13] Checking proof-relevant semantic adapters...")
    for label, content, pairs in (
        ("energy adapter", energy, (
            ("HardHighPassProjectorSelfAdjoint", "hardHighPassProjectorSelfAdjoint"),
            ("ProjectedConvectionTriadsExactlyEnumerated", "projectedConvectionTriadsExactlyEnumerated"),
        )),
        ("bootstrap adapter", bootstrap, (
            ("PhysicalEnergyIdentityMatchesCutoffData", "physicalEnergyIdentityMatchesCutoffData"),
            ("BootstrapDecayImpliesRegularity", "bootstrapDecayImpliesRegularity"),
        )),
        ("full-shell adapter", full_shell, (
            ("SelectedPairListIsHardHighPhysicalTriadImage", "selectedPairListIsHardHighPhysicalTriadImage"),
            ("ProfileSchurConstantUniformInCutoff", "profileSchurConstantUniformInCutoff"),
        )),
    ):
        for proposition, witness in pairs:
            require(content, proposition, label)
            require(content, witness, label)

    print("[13/13] Rejecting axioms and accidental promotion...")
    for name in NEW_AGDA:
        forbid(text[name], "\npostulate\n", name)
        forbid(text[name], "\npostulate ", name)
        forbid(text[name], "bkmExclusionProved = true", name)
        forbid(text[name], "clayNavierStokesPromoted = true", name)
        forbid(text[name], "RouteReadyForPromotion = true", name)

    print("PASS: Luo weighted-Schur flux tranche is attributed and fail-closed at the remaining physical seam.")
    print("NOTE: this is a static source audit; run the focused Agda checker separately.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
