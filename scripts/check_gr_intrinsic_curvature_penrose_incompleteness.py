#!/usr/bin/env python3
"""Focused static contract for intrinsic GR, causal-boundary authority, and Penrose incompleteness.

This remains structural. It verifies attribution/payment surfaces but does not
certify the continuum theorems or Agda kernel acceptance.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

INTRINSIC = ROOT / "DASHI/Physics/Gravity/IntrinsicSpacetimeCurvatureInterpretationExact.agda"
CAUSAL = ROOT / "DASHI/Physics/Gravity/CausalFutureHorismosNullGeneratorExact.agda"
FOCUSING = ROOT / "DASHI/Physics/Gravity/NullRaychaudhuriSachsFocusingExact.agda"
AUTHORITY = ROOT / "DASHI/Physics/Gravity/PenroseGlobalCausalityAuthorityExact.agda"
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
require(CAUSAL, ["futureHorismosEPlus", "futureHorismosIsAchronalBoundary", "generatorAfterConjugatePointLeavesHorismos"])
require(FOCUSING, ["negativeExpansionForcesFiniteAffineFocusing", "conjugatePointIsNotSpacetimeSingularity"])
require(AUTHORITY, [
    "Minguzzi2019LorentzianCausalitySourceReceipt",
    "propositionTwoOneFourThreeCausalSimplicityHorismosClosure",
    "theoremSixTwentyThreeNonCompactCauchyObstruction",
    "theoremSixTwentyThreeTimelikeFlowProjection",
    "globallyHyperbolicImpliesCausallySimpleForHorismosBoundary",
    "horismosAsBoundaryOfChronologicalFuture",
    "theoremSixTwentyFivePenroseComposition",
    "authorityCitationImportsNeitherProofNorAuthority",
    "authorityOwnerInternallyReprovesGlobalCausality",
])
require(GLOBAL, [
    "globalCausalityAuthorityConsumer",
    "sameHorismosObjectCarriesBothReductioClaims",
    "nonCompactCauchySurfaceForcesFutureHorismosNonCompact",
    "globalContradictionForcesNullIncompleteness",
])
require(PENROSE, ["Penrose1965SourceReceipt", "nullGeodesicIncompletenessConclusion"])
require(REGRESSION, [
    "globalAuthorityCitationNonPromotionRegression",
    "globalAuthorityDerivationStillClosedRegression",
    "globalCausalityDerivationStillClosedRegression",
    "continuumPromotionStillClosedRegression",
])
require(AGGREGATE, [
    "PenroseGlobalCausalityAuthorityExact",
    "PenroseGlobalHorismosContradictionExact",
])

print("GR global-causality authority / Penrose static contract: OK")
