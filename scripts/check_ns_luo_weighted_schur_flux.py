#!/usr/bin/env python3
"""Fail-closed static audit for the Luo weighted-Schur continuation tranche."""

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
    "finite_hermitian": CLOSURE / "NSTriadKNFiniteHermitianDiagonalMultiplierExact.agda",
    "coefficient_projector": CLOSURE / "NSTriadKNHardProjectorCoefficientSelfAdjointExact.agda",
    "parseval_projector": CLOSURE / "NSTriadKNHardProjectorParsevalTransportExact.agda",
    "radial_multiplier": CLOSURE / "NSTriadKNLuoRadialSmoothMultiplierExact.agda",
    "hard_smooth": CLOSURE / "NSTriadKNHardSmoothLittlewoodPaleyTransferExact.agda",
    "multiplier_authority": CLOSURE / "NSTriadKNLuoPeriodicMultiplierKernelBoundExact.agda",
    "flux": CLOSURE / "NSTriadKNPhysicalCutoffFluxWeightedSchurExact.agda",
    "reuse": CLOSURE / "NSTriadKNWeightedSchurPhysicalFluxReuseExact.agda",
    "physical_full_shell": CLOSURE / "NSTriadKNLuoHardHighFullShellPhysicalIdentificationExact.agda",
    "full_shell": CLOSURE / "NSTriadKNLuoFullShellFluxAdapterExact.agda",
    "energy": CLOSURE / "NSTriadKNProjectedConvectionEnergyFluxExact.agda",
    "bootstrap": CLOSURE / "NSTriadKNLuoCutoffEnergyBootstrapExact.agda",
    "physical_time": CLOSURE / "NSTriadKNLuoPhysicalEnergyDissipationTimeExact.agda",
    "published_luo": CLOSURE / "NSTriadKNLuoPublishedContinuationAuthorityExact.agda",
    "synthesis": CLOSURE / "NSTriadKNLuoWeightedSchurContinuationSynthesisExact.agda",
    "integration": CLOSURE / "NSTriadKNLuoWeightedSchurFluxIntegration.agda",
    "top": CLOSURE / "NSTriadKNLocalizedBKMRouteIntegration.agda",
    "weighted_schur": CLOSURE / "NSTriadKNWeightedSchurProductBound.agda",
    "physical_triads": CLOSURE / "NSTriadKNPhysicalTriadEnumeration.agda",
    "physical_fibre": CLOSURE / "NSTriadKNValidatedPhysicalFiberImage.agda",
    "full_shell_existing": CLOSURE / "NSCompactGammaFullShellSchur.agda",
    "coherence_existing": CLOSURE / "NSCompactGammaTriadFullShellCoherence.agda",
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
    "finite_hermitian",
    "coefficient_projector",
    "parseval_projector",
    "radial_multiplier",
    "hard_smooth",
    "multiplier_authority",
    "flux",
    "reuse",
    "physical_full_shell",
    "full_shell",
    "energy",
    "bootstrap",
    "physical_time",
    "published_luo",
    "synthesis",
    "integration",
)


def fail(message: str) -> None:
    print(f"FAIL: {message}")
    raise SystemExit(1)


def require(text: str, needle: str, label: str) -> None:
    if needle not in text:
        fail(f"{label}: missing {needle!r}")


def require_all(text: str, needles: tuple[str, ...], label: str) -> None:
    for needle in needles:
        require(text, needle, label)


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


def main() -> int:
    text = load()

    print("[1/12] Luo source and scale fidelity")
    require_all(text["source"], (
        "10.1007/s00021-019-0411-z",
        "fullLowPassGradientInfinityIntegral",
        "viscosityNormalizedToOne",
        "LuoProposition31FluxTarget",
        "fluxBoundByEnergyMajorantTimesLowPassGradient",
        "LuoSmallTimeEnergyDissipationTarget",
    ), "Luo source architecture")
    require_all(text["scale"], (
        "shellIndexRole",
        "dyadicWavenumberRole",
        "parabolicDenominatorRole",
        "finiteModeCountRole",
        "profileDepthRole",
        "galerkinCutoffRole",
        "localizedBKMScaleRolesSeparated = true",
    ), "scale dictionary")
    require(text["dictionary"],
            "Weighted Schur is used on the flux/energy factor",
            "markdown dictionary")

    print("[2/12] Exact physical enumeration and hard selection")
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
        "filterHighSound",
        "filterHighComplete",
        "filterHighNoDuplicates",
        "hardHighPhysicalTriadSelectionSound",
        "hardHighPhysicalTriadSelectionComplete",
        "hardHighPhysicalTriadNoDuplicates",
        "hardHighOutputSelectionConstructed = true",
        "hardLowHighPartitionConstructed = true",
    ), "hard high selector")
    require(text["physical_triads"],
            "physicalTriadEnumerationImplemented = true",
            "literal physical triads")
    require(text["physical_fibre"],
            "validatedPhysicalFiberImageConstructed = true",
            "physical fibre")

    print("[3/12] Finite Hermitian projector closure")
    require_all(text["finite_hermitian"], (
        "diagonalTermSelfAdjoint",
        "finiteDiagonalMultiplierSelfAdjoint",
        "finiteDiagonalMultiplierIdempotent",
        "finiteHermitianDiagonalSelfAdjointnessConstructed = true",
        "finiteHermitianDiagonalIdempotenceConstructed = true",
    ), "finite Hermitian multiplier")
    require_all(text["coefficient_projector"], (
        "hardLowCoefficientSelfAdjoint",
        "hardHighCoefficientSelfAdjoint",
        "hardLowCoefficientIdempotent",
        "hardHighCoefficientIdempotent",
        "hardProjectorCoefficientSelfAdjointnessClosed = true",
    ), "coefficient projector")
    require_all(text["parseval_projector"], (
        "PeriodicHermitianParsevalTransport",
        "hardLowPhysicalSelfAdjoint",
        "hardHighPhysicalSelfAdjoint",
        "HardProjectorOrthogonalCertificate",
        "coefficientUnitaryHardProjectorOrthogonal",
        "hardProjectorOrthogonalCertificateConstructed = true",
    ), "Parseval projector transport")

    print("[4/12] Luo radial support and hard/smooth comparison")
    require_all(text["radial_multiplier"], (
        "symbolIsOneOnInnerThreeQuarterBall",
        "symbolVanishesOutsideUnitBall",
        "smoothSupportInsideHardNext",
        "smoothLowPassFactorsThroughHardNext",
        "derivativeBernsteinConstant",
        "finiteModeL2ToLInfinityConstant",
        "hardSmoothMultiplierLInfinityConstant",
        "smoothHardNextSupportFactorizationConstructed = true",
        "localizedMultiplierConstantsSeparated = true",
    ), "radial multiplier")
    require_all(text["hard_smooth"], (
        "HardSmoothTerminalWindowComparison",
        "hardTerminalWindowBudgetTransfersToLuoSmoothCriterion",
        "hardSmoothTerminalWindowTransferConstructed = true",
    ), "hard-smooth transfer")
    require_all(text["multiplier_authority"], (
        "PublishedLuoPeriodicMultiplierKernelAuthority",
        "smoothGradientKernelEstimate",
        "smoothTerminalWindowKernelEstimate",
        "dyadicKernelL1BoundUniformInShell",
        "luoSmoothCriterionFromHardBudget",
        "luoPeriodicMultiplierKernelBoundLevel = standardImported",
        "concretePublishedLuoMultiplierAuthoritySelected = false",
    ), "periodic multiplier authority")

    print("[5/12] Pair-incidence multiplicity and Hermitian flux majorants")
    require_all(text["enumeration"], (
        "ExactFiniteEnumeration",
        "NoDuplicates",
        "PairIncidenceSlot",
        "triadContributesExactlyThreeIncidences",
        "PhysicalFibreMultiplicityAgreement",
        "fibreLengthsAgree",
    ), "enumeration interface")
    require_all(text["flux"], (
        "complexDifferenceNormSquared",
        "HermitianPairIncidenceAtom",
        "physicalTriadTermDominatedByIncidenceMajorant",
        "fiberMultiplicityMatchesConvolutionMultiplicity",
        "physicalMajorantEqualsProfileSum",
        "physicalCutoffFluxDominatedByPairIncidenceFold",
        "physicalCutoffFluxDominatedByWeightedSchurMajorant",
        "luoCutoffFluxEstimate",
        "physicalWeightedSchurBridgeInhabited = false",
    ), "Hermitian flux theorem")

    print("[6/12] Hard-high physical/full-shell representation")
    require_all(text["physical_full_shell"], (
        "HardHighPhysicalFullShellIdentification",
        "selectedPhysicalListIsFullShellPairList",
        "physicalSignedCoefficientDominated",
        "hardHighPhysicalFullShellRepresentationTheoremConstructed = true",
        "physicalSignedCoefficientDominationTheoremConstructed = true",
        "canonicalHardHighPhysicalFullShellIdentificationInhabited = false",
    ), "physical full-shell identification")
    require_all(text["coherence_existing"], (
        "pairListsMatch",
        "signedResponseMatchesFullShell",
        "localMajorantMatchesFullShell",
        "coherentLocalMajorization",
    ), "existing triad/full-shell coherence")

    print("[7/12] Existing weighted-Schur and full-shell reuse")
    require_all(text["reuse"], (
        "weightedSchurProductBoundClosed ≡ true",
        "weightedSchurMatrixOperatorDataClosed ≡ false",
        "weightedSchurRelevantToLuoFluxRoute = true",
    ), "weighted-Schur reuse")
    require(text["weighted_schur"],
            "weightedSchurProductBoundClosed = true",
            "existing Schur algebra")
    require_all(text["full_shell"], (
        "Closure.closureNearResponseMajorized",
        "luoFullShellCutoffFluxEstimate",
        "matureFullShellNearMajorizationReused = true",
        "matureFullShellUniformSchurReused = true",
        "luoFullShellPhysicalIdentificationInhabited = false",
    ), "full-shell Luo adapter")
    require_all(text["full_shell_existing"], (
        "everyLocalFourierMajorization",
        "certificateAt",
    ), "existing full shell")

    print("[8/12] Projected energy and literal time transport")
    require_all(text["energy"], (
        "ProjectedCutoffEnergyBalance",
        "divergenceFreePressureCancellation",
        "highFrequencyEnergyInequality",
        "projectedEnergyControlledByWeightedSchurFlux",
        "periodicHardHighPassSelfAdjointnessClosedIsTrue",
        "literalProjectedConvectionEnumerationClosedIsTrue",
        "periodicProjectedConvectionFluxAdapterInhabited = false",
    ), "projected energy flux")
    require_all(text["bootstrap"], (
        "LuoParabolicTimeCutoff",
        "LuoCutoffEnergyFluxData",
        "localizedGradientSubstitution",
        "luoSmallTimeEnergyDissipationRecursion",
        "LuoCutoffBootstrapCertificate",
        "luoCutoffBootstrapBound",
        "physicalLuoBootstrapAdapterInhabited = false",
    ), "Luo bootstrap")
    require_all(text["physical_time"], (
        "LiteralLuoCutoffEnergyDissipationTimeIdentification",
        "previousEnergyMeaning",
        "currentEnergyMeaning",
        "dissipationMeaning",
        "integratedFluxMeaning",
        "weightedShellEnergyMeaning",
        "localizedGradientIntegralMeaning",
        "literalPhysicalLuoEnergyDissipationRecursion",
        "literalPhysicalLuoBootstrapBound",
        "canonicalLiteralLuoPhysicalIdentificationInhabited = false",
    ), "literal physical time transport")

    print("[9/12] Published Luo authority and final synthesis")
    require_all(text["published_luo"], (
        "PublishedLuoTheorem11Authority",
        "LuoLocalizedGradientLimsupBound",
        "theorem11Regularity",
        "luoTheorem11Continuation",
        "LuoRepositoryHypothesisIdentification",
        "luoContinuationFromRepositoryLimsup",
        "luoTheorem11AuthorityLevel = standardImported",
        "selectedPublishedLuoAuthorityInhabited = false",
    ), "published Luo authority")
    require_all(text["synthesis"], (
        "LuoWeightedSchurContinuationSynthesis",
        "hardHighPhysicalListMatchesFullShell",
        "hardHighPhysicalCoefficientDominated",
        "literalPhysicalCutoffRecursion",
        "smoothLuoCutoffBound",
        "luoWeightedSchurContinuation",
        "luoWeightedSchurContinuationSynthesisConstructed = true",
        "canonicalLuoWeightedSchurContinuationSynthesisInhabited = false",
    ), "final continuation synthesis")

    print("[10/12] Consolidated fail-closed ledger")
    require_all(text["integration"], (
        "finiteHermitianSelfAdjointnessConstructed",
        "hardProjectorOrthogonalCertificateConstructed",
        "smoothHardNextFactorizationConstructed",
        "periodicMultiplierAuthoritySurfaceConstructed",
        "hardHighFullShellRepresentationTheoremConstructed",
        "physicalSignedCoefficientDominationTheoremConstructed",
        "hardHighSelfAdjointnessClosed",
        "literalPhysicalEnergyTimeInterfaceConstructed",
        "publishedLuoContinuationAdapterConstructed",
        "finalContinuationSynthesisConstructed",
        "canonicalContinuationSynthesisOpen",
        "luoWeightedSchurFluxTrancheComplete = true",
        "luoWeightedSchurFluxRouteReadyForPromotion = false",
        "existingBKMExclusionStillFalse",
        "existingClayPromotionStillFalse",
    ), "flux integration")
    require_all(text["top"], (
        "hardProjectorOrthogonalCertificateConstructed",
        "luoRadialSupportFactorizationConstructed",
        "conditionalContinuationSynthesisConstructed",
        "localizedBKMRouteReadyForPromotion = false",
    ), "top integration")
    require(text["pair_bounds"],
            "canonicalBKMExclusionProved = false",
            "legacy BKM gate")

    print("[11/12] Proof-relevant semantic boundaries")
    for label, content, pairs in (
        ("physical full-shell", text["physical_full_shell"], (
            ("selectedPhysicalListIsPairAtoms", "physicalSignedMagnitudeAgreement"),
            ("physicalIncidenceMajorantAgreement", "decodeEncode"),
        )),
        ("physical time", text["physical_time"], (
            ("PhysicalEnergyIsHardHighL2Squared", "physicalEnergyIsHardHighL2Squared"),
            ("PhysicalGradientIntegralIsLuoLowPassIntegral", "physicalGradientIntegralIsLuoLowPassIntegral"),
        )),
        ("published Luo", text["published_luo"], (
            ("RepositoryLocalizedLimsupWitness", "repositoryLocalizedLimsupWitness"),
            ("repositoryLimsupMatchesLuoHypothesis", "solutionSolves"),
        )),
    ):
        for proposition, witness in pairs:
            require(content, proposition, label)
            require(content, witness, label)

    print("[12/12] Rejecting new axioms and accidental promotion")
    for name in NEW_AGDA:
        forbid(text[name], "\npostulate\n", name)
        forbid(text[name], "\npostulate ", name)
        forbid(text[name], "bkmExclusionProved = true", name)
        forbid(text[name], "clayNavierStokesPromoted = true", name)
        forbid(text[name], "RouteReadyForPromotion = true", name)

    print("PASS: Luo weighted-Schur continuation tranche is attributed and fail-closed at the canonical physical inhabitant.")
    print("NOTE: this is a static source audit; run the focused Agda checker separately.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
