#!/usr/bin/env python3
"""Focused static contract for intrinsic GR, causal boundary structure, null focusing, and Penrose incompleteness.

This is intentionally structural. It does not certify the continuum equations,
causal-boundary theorems, or Penrose theorem themselves.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

INTRINSIC = ROOT / "DASHI/Physics/Gravity/IntrinsicSpacetimeCurvatureInterpretationExact.agda"
CAUSAL = ROOT / "DASHI/Physics/Gravity/CausalFutureHorismosNullGeneratorExact.agda"
FOCUSING = ROOT / "DASHI/Physics/Gravity/NullRaychaudhuriSachsFocusingExact.agda"
GLOBAL = ROOT / "DASHI/Physics/Gravity/PenroseGlobalHorismosContradictionExact.agda"
PENROSE = ROOT / "DASHI/Physics/Gravity/Penrose1965NullGeodesicIncompletenessExact.agda"
REGRESSION = ROOT / "DASHI/Physics/Gravity/IntrinsicPenroseInterpretationRegression.agda"
AGGREGATE = ROOT / "DASHI/Physics/PhysicsKernelClosure.agda"


def require(path: Path, needles: list[str]) -> None:
    if not path.exists():
        raise SystemExit(f"missing required file: {path.relative_to(ROOT)}")
    text = path.read_text(encoding="utf-8")
    missing = [needle for needle in needles if needle not in text]
    if missing:
        raise SystemExit(f"{path.relative_to(ROOT)} missing required surfaces: {missing}")

require(INTRINSIC, ["rubberSheetEmbeddingIsNotIntrinsicLorentzianCurvature", "timeCurvesIntoSpacePhraseIsNotInvariantGRStatement"])
require(CAUSAL, [
    "chronologicalFutureIPlus",
    "causalFutureJPlus",
    "futureHorismosEPlus",
    "horismosEqualsCausalMinusChronologicalFuture",
    "futureHorismosIsAchronalBoundary",
    "futureHorismosGeneratedByNullGeodesics",
    "conjugatePointForcesGeneratorIntoChronologicalFuture",
    "generatorAfterConjugatePointLeavesHorismos",
    "causalFutureIsNotChronologicalFuture",
    "horismosIsNotEventHorizon",
    "causalBoundaryOwnerInternallyReprovesContinuumCausality",
])
require(FOCUSING, ["negativeExpansionForcesFiniteAffineFocusing", "conjugatePointIsNotSpacetimeSingularity"])
require(GLOBAL, [
    "futureHorismosOfTrappedSurface",
    "sameHorismosObjectCarriesBothReductioClaims",
    "causalBoundaryConsumer",
    "nullCompletenessPlusFocusingMakesFutureHorismosCompact",
    "globalContradictionForcesNullIncompleteness",
])
require(PENROSE, ["Penrose1965SourceReceipt", "nullGeodesicIncompletenessConclusion"])
require(REGRESSION, [
    "causalVsChronologicalFutureFirewallRegression",
    "horismosNotEventHorizonRegression",
    "causalBoundaryDerivationStillClosedRegression",
    "globalCausalityDerivationStillClosedRegression",
    "continuumPromotionStillClosedRegression",
])
require(AGGREGATE, [
    "CausalFutureHorismosNullGeneratorExact",
    "NullRaychaudhuriSachsFocusingExact",
    "PenroseGlobalHorismosContradictionExact",
])

print("GR causal-boundary / focusing / global Penrose static contract: OK")
