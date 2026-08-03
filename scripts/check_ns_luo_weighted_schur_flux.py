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
    "flux": CLOSURE / "NSTriadKNPhysicalCutoffFluxWeightedSchurExact.agda",
    "reuse": CLOSURE / "NSTriadKNWeightedSchurPhysicalFluxReuseExact.agda",
    "energy": CLOSURE / "NSTriadKNProjectedConvectionEnergyFluxExact.agda",
    "bootstrap": CLOSURE / "NSTriadKNLuoCutoffEnergyBootstrapExact.agda",
    "integration": CLOSURE / "NSTriadKNLuoWeightedSchurFluxIntegration.agda",
    "top": CLOSURE / "NSTriadKNLocalizedBKMRouteIntegration.agda",
    "weighted_schur": CLOSURE / "NSTriadKNWeightedSchurProductBound.agda",
    "pair_bounds": CLOSURE / "NSTriadKNPairIncidenceProfileBounds.agda",
    "dictionary": ROOT / "docs" / "ns-localized-bkm-variable-dictionary.md",
}

NEW_AGDA = (
    "scale",
    "source",
    "enumeration",
    "flux",
    "reuse",
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

    print("[1/9] Checking Luo source fidelity...")
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

    print("[2/9] Checking scale-role separation...")
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

    print("[3/9] Checking multiplicity-safe enumeration...")
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
        require(enumeration, token, "projected enumeration")

    print("[4/9] Checking Hermitian physical-flux domination...")
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

    print("[5/9] Checking existing weighted-Schur reuse...")
    reuse = text["reuse"]
    require(reuse, "weightedSchurProductBoundClosed ≡ true", "Schur reuse")
    require(reuse, "weightedSchurMatrixOperatorDataClosed ≡ false", "Schur concrete gate")
    require(reuse, "weightedSchurRelevantToLuoFluxRoute = true", "Schur relevance")
    require(text["weighted_schur"], "weightedSchurProductBoundClosed = true", "existing Schur algebra")

    print("[6/9] Checking projected energy-flux composition...")
    energy = text["energy"]
    for token in (
        "ProjectedCutoffEnergyBalance",
        "divergenceFreePressureCancellation",
        "highFrequencyEnergyInequality",
        "PeriodicProjectedConvectionFluxAdapter",
        "hardHighPassProjectorSelfAdjoint",
        "projectedEnergyControlledByWeightedSchurFlux",
    ):
        require(energy, token, "projected energy flux")
    require(energy, "periodicProjectedConvectionFluxAdapterInhabited = false", "projected physical gate")

    print("[7/9] Checking Luo bootstrap algebra...")
    bootstrap = text["bootstrap"]
    for token in (
        "LuoParabolicTimeCutoff",
        "LuoCutoffEnergyFluxData",
        "localizedGradientSubstitution",
        "luoSmallTimeEnergyDissipationRecursion",
        "LuoCutoffBootstrapCertificate",
        "luoCutoffBootstrapBound",
    ):
        require(bootstrap, token, "Luo bootstrap")
    require(bootstrap, "physicalLuoBootstrapAdapterInhabited = false", "bootstrap physical gate")

    print("[8/9] Checking integrated fail-closed ledger...")
    integration = text["integration"]
    for token in (
        "luoWeightedSchurFluxTrancheComplete = true",
        "luoWeightedSchurFluxRouteReadyForPromotion = false",
        "existingBKMExclusionStillFalse",
        "existingClayPromotionStillFalse",
    ):
        require(integration, token, "flux integration")
    require(text["top"], "weightedSchurFluxTrancheConstructed", "top integration")
    require(text["pair_bounds"], "canonicalBKMExclusionProved = false", "legacy BKM gate")

    print("[9/9] Rejecting axioms and accidental promotion...")
    for name in NEW_AGDA:
        forbid(text[name], "\npostulate\n", name)
        forbid(text[name], "\npostulate ", name)
        forbid(text[name], "bkmExclusionProved = true", name)
        forbid(text[name], "clayNavierStokesPromoted = true", name)
        forbid(text[name], "RouteReadyForPromotion = true", name)

    print("PASS: Luo weighted-Schur flux tranche is attributed and fail-closed at the physical seam.")
    print("NOTE: this is a static source audit; run the focused Agda checker separately.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
