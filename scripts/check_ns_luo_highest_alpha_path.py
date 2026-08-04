#!/usr/bin/env python3
"""Verify the machine-visible highest-alpha Navier--Stokes path."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FOUNDATION = ROOT / "DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaFiniteFourierFoundationExact.agda"
CUTSET = ROOT / "DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaCriticalCutsetExact.agda"
COMPOSITION = ROOT / "DASHI/Physics/Closure/NSTriadKNLuoHighestAlphaPathCompositionExact.agda"

EXPECTED = [
    "officialWeightedSpatialIntegralFourierIdentity",
    "rp1PairCoefficientIdentification",
    "rp2PairCoefficientIdentification",
    "tailPairCoefficientIdentification",
    "officialMultiplierReceiptsInhabited",
    "sourceAbsoluteFluxMatchesPhysicalBridge",
    "sourceLowGradientMatchesPhysicalBridge",
    "sourceEnergyDominatedByCommonSchurWeightedEnergy",
    "physicalFluxBelowLowGradientTimesWeightedEnergy",
    "officialEquation42",
    "physicalRHSMatchesTotalInteractionFold",
    "physicalJ11LowerBound",
    "physicalJ11UpperBound",
    "physicalJ12Bound",
    "physicalJ2Bound",
    "analyticFourShellRatioEqualsQuarter",
    "integralGronwall",
    "integratedCutoffEnergyInequality",
    "fluxCorrectionAbsorbedUniformly",
    "physicalBlockDecayCertificate",
    "shellDecayImpliesContinuationRegularity",
    "canonicalAnalyticPhysicalLeaves",
    "finiteMaximalTimeExcludedForEveryDatum",
    "officialInfiniteRealAnalyticInputs",
    "globalStrongSolutionForEveryAdmissibleDatum",
    "globalVelocitySmooth",
    "globalPressureSmooth",
    "submissionAuditReceiptComplete",
]

EXPECTED_PHASES = {
    **{name: 1 for name in EXPECTED[0:4]},
    **{name: 2 for name in EXPECTED[4:9]},
    **{name: 3 for name in EXPECTED[9:11]},
    **{name: 4 for name in EXPECTED[11:15]},
    **{name: 5 for name in EXPECTED[15:21]},
    EXPECTED[21]: 6,
    EXPECTED[22]: 7,
    EXPECTED[23]: 8,
    **{name: 9 for name in EXPECTED[24:27]},
    EXPECTED[27]: 10,
}

REQUIRED_FOUNDATION_REUSE = [
    "Official.officialHardProjectorOrthogonal",
    "Hard.lowProjectorIdempotent",
    "Hard.highProjectorIdempotent",
    "Hard.lowAfterHighIsZero",
    "Hard.highAfterLowIsZero",
    "Hard.highProjectorCommutesWithDerivative",
    "Hard.highProjectorCommutesWithCurl",
    "finiteHermitianParsevalFoundationClosed = true",
    "hardProjectorOrthogonalityFoundationClosed = true",
    "hardProjectorDifferentialCommutationFoundationClosed = true",
    "continuumTorusIntegralIdentificationClosed = false",
]

REQUIRED_COMPOSITIONS = [
    "Weighted.weightedIncrementFourierRealization",
    "Pairs.threePairWholeFoldReceipt",
    "StageB.officialMultiplierRealizationFromFiniteReceipts",
    "StageB.canonicalWeightedSchurFromPhysicalLeaves",
    "Equation42.equation42FinitePhysicalInputs",
    "Section4.section4ComponentBounds",
    "Fractional.analyticFourShellRatioIdentification",
    "Gronwall.meanValueGronwallReceipt",
    "Block.physicalBlockDecayReceipt",
    "Promotion.physicalSchurBoundAtInfiniteCutoff",
    "Promotion.physicalEquation42AtInfiniteCutoff",
    "Promotion.physicalFluxIdentityAtInfiniteCutoff",
    "Critical.criticalPathCanonicalInputs",
    "Critical.criticalPathContradictsSelectedFiniteMaximality",
    "Final.submissionReadyTheoremFromUniformPhysicalConstruction",
]


def between(text: str, start: str, end: str) -> str:
    try:
        return text.split(start, 1)[1].split(end, 1)[0]
    except IndexError as exc:
        raise SystemExit(f"cannot locate section between {start!r} and {end!r}") from exc


def parse_constructors(text: str) -> list[str]:
    body = between(text, "data CriticalLemma : Set where", ": CriticalLemma")
    return re.findall(r"^\s{2}([A-Za-z][A-Za-z0-9]*)\s*$", body, re.MULTILINE)


def parse_phases(text: str) -> dict[str, int]:
    return {
        name: int(phase)
        for name, phase in re.findall(
            r"^criticalPhase\s+([A-Za-z][A-Za-z0-9]*)\s*=\s*(\d+)\s*$",
            text,
            re.MULTILINE,
        )
    }


def parse_predecessors(text: str) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    starts = list(
        re.finditer(
            r"^criticalPredecessors\s+([A-Za-z][A-Za-z0-9]*)\s*=",
            text,
            re.MULTILINE,
        )
    )
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else text.find(
            "\ncriticalLemmaCount", match.end()
        )
        if end < 0:
            raise SystemExit("cannot find end of predecessor definitions")
        block = text[match.end():end]
        tokens = re.findall(r"\b[A-Za-z][A-Za-z0-9]*\b", block)
        result[match.group(1)] = [token for token in tokens if token in EXPECTED]
    return result


def main() -> int:
    if not FOUNDATION.exists() or not CUTSET.exists() or not COMPOSITION.exists():
        raise SystemExit("highest-alpha modules are missing")

    foundation_text = FOUNDATION.read_text(encoding="utf-8")
    cutset_text = CUTSET.read_text(encoding="utf-8")
    composition_text = COMPOSITION.read_text(encoding="utf-8")

    for declaration in REQUIRED_FOUNDATION_REUSE:
        if declaration not in foundation_text:
            raise SystemExit(f"missing finite Fourier foundation reuse: {declaration}")

    constructors = parse_constructors(cutset_text)
    if constructors != EXPECTED:
        raise SystemExit(
            "critical constructor order mismatch\n"
            f"expected={EXPECTED}\nfound={constructors}"
        )
    if len(set(constructors)) != 28:
        raise SystemExit("critical cutset must contain 28 unique declarations")

    phases = parse_phases(cutset_text)
    if phases != EXPECTED_PHASES:
        raise SystemExit(f"critical phase map mismatch: {phases}")

    predecessors = parse_predecessors(cutset_text)
    if set(predecessors) != set(EXPECTED):
        missing = sorted(set(EXPECTED) - set(predecessors))
        extra = sorted(set(predecessors) - set(EXPECTED))
        raise SystemExit(f"predecessor coverage mismatch; missing={missing}, extra={extra}")

    position = {name: index for index, name in enumerate(EXPECTED)}
    for target, sources in predecessors.items():
        for source in sources:
            if position[source] >= position[target]:
                raise SystemExit(
                    f"non-topological dependency: {source} -> {target}"
                )

    required_fail_closed = [
        "highestAlphaCriticalCutsetInhabited = false",
        "canonicalAnalyticPhysicalLeavesInhabited = false",
        "periodicNavierStokesGlobalRegularityProved = false",
        "submissionPackageComplete = false",
    ]
    for entry in required_fail_closed:
        if entry not in cutset_text:
            raise SystemExit(f"missing fail-closed declaration: {entry}")

    for composition in REQUIRED_COMPOSITIONS:
        if composition not in composition_text:
            raise SystemExit(f"missing highest-alpha composition: {composition}")

    all_agda = [
        path for path in (ROOT / "DASHI/Physics/Closure").glob("NSTriadKNLuo*.agda")
        if path != CUTSET
    ]
    corpus = "\n".join(path.read_text(encoding="utf-8").lower() for path in all_agda)
    missing_existing = [name for name in EXPECTED if name.lower() not in corpus]
    if missing_existing:
        raise SystemExit(
            "critical names not connected to existing in-repo declarations or "
            "inventories: " + ", ".join(missing_existing)
        )

    print(
        "Highest-alpha Luo path verified: finite Fourier foundation reused; "
        "28 declarations; 10 phases; topological predecessors; "
        "existing-repository coverage; closed reducers; fail-closed frontier."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
