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

NEW_AGDA = tuple(name for name in FILES if name not in {
    "weighted_schur", "physical_triads", "physical_fibre",
    "full_shell_existing", "coherence_existing", "pair_bounds", "dictionary",
})


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

    print("[1/10] Source and scale fidelity")
    require_all(t["source"], (
        "10.1007/s00021-019-0411-z",
        "fullLowPassGradientInfinityIntegral",
        "viscosityNormalizedToOne",
        "fluxBoundByEnergyMajorantTimesLowPassGradient",
    ), "Luo source")
    require_all(t["scale"], (
        "shellIndexRole", "dyadicWavenumberRole",
        "finiteModeCountRole", "profileDepthRole", "galerkinCutoffRole",
        "localizedBKMScaleRolesSeparated = true",
    ), "scale dictionary")
    require_all(t["dictionary"], (
        "Never rewrite `(N + 1)^-1`",
        "Weighted Schur is used on the flux/energy factor",
    ), "markdown dictionary")

    print("[2/10] Physical enumeration and multiplicity")
    require_all(t["physical_reuse"], (
        "physicalTriadEnumerationImplementedIsTrue",
        "hardProjectedHighFrequencySelectionConstructed = true",
        "validatedPhysicalFiberImageConstructedIsTrue",
    ), "physical reuse")
    require_all(t["hard_selection"], (
        "hardHighPhysicalTriadSelectionSound",
        "hardHighPhysicalTriadSelectionComplete",
        "hardHighPhysicalTriadNoDuplicates",
    ), "hard selector")
    require_all(t["enumeration"], (
        "triadContributesExactlyThreeIncidences",
        "PhysicalFibreMultiplicityAgreement",
        "fibreLengthsAgree",
    ), "incidence enumeration")

    print("[3/10] Orthogonal hard projector")
    require_all(t["finite_hermitian"], (
        "diagonalTermSelfAdjoint",
        "finiteDiagonalMultiplierSelfAdjoint",
        "finiteHermitianDiagonalSelfAdjointnessConstructed = true",
    ), "finite Hermitian theorem")
    require_all(t["coefficient_projector"], (
        "hardLowCoefficientSelfAdjoint",
        "hardHighCoefficientSelfAdjoint",
        "hardProjectorCoefficientSelfAdjointnessClosed = true",
    ), "coefficient projector")
    require_all(t["parseval_projector"], (
        "PeriodicHermitianParsevalTransport",
        "HardProjectorOrthogonalCertificate",
        "coefficientUnitaryHardProjectorOrthogonal",
        "hardProjectorOrthogonalCertificateConstructed = true",
    ), "Parseval transport")

    print("[4/10] Radial multiplier and terminal-window transfer")
    require_all(t["radial_multiplier"], (
        "symbolIsOneOnInnerThreeQuarterBall",
        "symbolVanishesOutsideUnitBall",
        "smoothLowPassFactorsThroughHardNext",
        "derivativeBernsteinConstant",
        "finiteModeL2ToLInfinityConstant",
        "hardSmoothMultiplierLInfinityConstant",
        "localizedMultiplierConstantsSeparated = true",
    ), "radial multiplier")
    require_all(t["hard_smooth"], (
        "hardTerminalWindowBudgetTransfersToLuoSmoothCriterion",
        "hardSmoothTerminalWindowTransferConstructed = true",
    ), "hard/smooth transfer")
    require_all(t["multiplier_authority"], (
        "PublishedLuoPeriodicMultiplierKernelAuthority",
        "dyadicKernelL1BoundUniformInShell",
        "luoSmoothCriterionFromHardBudget",
        "luoPeriodicMultiplierKernelBoundLevel = standardImported",
        "concretePublishedLuoMultiplierAuthoritySelected = false",
    ), "multiplier authority")

    print("[5/10] Hermitian flux and weighted Schur")
    require_all(t["flux"], (
        "HermitianPairIncidenceAtom",
        "physicalTriadTermDominatedByIncidenceMajorant",
        "physicalCutoffFluxDominatedByWeightedSchurMajorant",
        "luoCutoffFluxEstimate",
        "physicalWeightedSchurBridgeInhabited = false",
    ), "flux theorem")
    require_all(t["reuse"], (
        "weightedSchurProductBoundClosed ≡ true",
        "weightedSchurRelevantToLuoFluxRoute = true",
    ), "Schur reuse")
    require_all(t["weighted_schur"], (
        "weightedSchurProductBoundClosed = true",
    ), "existing Schur theorem")

    print("[6/10] Physical/full-shell representation")
    require_all(t["physical_full_shell"], (
        "HardHighPhysicalFullShellIdentification",
        "selectedPhysicalListIsFullShellPairList",
        "physicalSignedCoefficientDominated",
        "physicalSignedCoefficientDominationTheoremConstructed = true",
        "canonicalHardHighPhysicalFullShellIdentificationInhabited = false",
    ), "physical/full-shell theorem")
    require_all(t["coherence_existing"], (
        "pairListsMatch", "coherentLocalMajorization",
    ), "existing coherence")
    require_all(t["full_shell"], (
        "luoFullShellCutoffFluxEstimate",
        "matureFullShellUniformSchurReused = true",
        "luoFullShellPhysicalIdentificationInhabited = false",
    ), "full-shell adapter")

    print("[7/10] Energy, time and bootstrap transport")
    require_all(t["energy"], (
        "highFrequencyEnergyInequality",
        "projectedEnergyControlledByWeightedSchurFlux",
        "periodicHardHighPassSelfAdjointnessClosedIsTrue",
        "literalProjectedConvectionEnumerationClosedIsTrue",
        "periodicProjectedConvectionFluxAdapterInhabited = false",
    ), "energy flux")
    require_all(t["bootstrap"], (
        "luoSmallTimeEnergyDissipationRecursion",
        "luoCutoffBootstrapBound",
        "physicalLuoBootstrapAdapterInhabited = false",
    ), "bootstrap")
    require_all(t["physical_time"], (
        "LiteralLuoCutoffEnergyDissipationTimeIdentification",
        "physicalEnergyIsHardHighL2Squared",
        "physicalGradientIntegralIsLuoLowPassIntegral",
        "literalPhysicalLuoEnergyDissipationRecursion",
        "canonicalLiteralLuoPhysicalIdentificationInhabited = false",
    ), "physical time")

    print("[8/10] Published Luo theorem and final synthesis")
    require_all(t["published_luo"], (
        "PublishedLuoTheorem11Authority",
        "theorem11Regularity",
        "luoTheorem11Continuation",
        "RepositoryLocalizedLimsupWitness",
        "repositoryLocalizedLimsupWitness",
        "repositoryLimsupMatchesLuoHypothesis",
        "luoTheorem11AuthorityLevel = standardImported",
        "selectedPublishedLuoAuthorityInhabited = false",
    ), "published Luo authority")
    require_all(t["synthesis"], (
        "LuoWeightedSchurContinuationSynthesis",
        "hardHighPhysicalListMatchesFullShell",
        "hardHighPhysicalCoefficientDominated",
        "literalPhysicalCutoffRecursion",
        "smoothLuoCutoffBound",
        "luoWeightedSchurContinuation",
        "canonicalLuoWeightedSchurContinuationSynthesisInhabited = false",
    ), "continuation synthesis")

    print("[9/10] Integrated fail-closed ledger")
    require_all(t["integration"], (
        "hardProjectorOrthogonalCertificateConstructed",
        "smoothHardNextFactorizationConstructed",
        "physicalSignedCoefficientDominationTheoremConstructed",
        "literalPhysicalEnergyTimeInterfaceConstructed",
        "publishedLuoContinuationAdapterConstructed",
        "finalContinuationSynthesisConstructed",
        "canonicalContinuationSynthesisOpen",
        "luoWeightedSchurFluxRouteReadyForPromotion = false",
        "existingBKMExclusionStillFalse",
        "existingClayPromotionStillFalse",
    ), "integration receipt")
    require_all(t["top"], (
        "conditionalContinuationSynthesisConstructed",
        "canonicalContinuationSynthesisStillOpen",
        "localizedBKMRouteReadyForPromotion = false",
    ), "top receipt")
    require_all(t["pair_bounds"], (
        "canonicalBKMExclusionProved = false",
    ), "legacy BKM gate")

    print("[10/10] Rejecting axioms and accidental promotion")
    for name in NEW_AGDA:
        forbid(t[name], "\npostulate\n", name)
        forbid(t[name], "\npostulate ", name)
        forbid(t[name], "bkmExclusionProved = true", name)
        forbid(t[name], "clayNavierStokesPromoted = true", name)
        forbid(t[name], "RouteReadyForPromotion = true", name)

    print("PASS: Luo continuation tranche is attributed and fail-closed at the canonical physical inhabitant.")
    print("NOTE: this is a static source audit; run the focused Agda checker separately.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
