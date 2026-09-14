#!/usr/bin/env python3
"""Focused static contract for intrinsic GR, causal-boundary authority, and Penrose incompleteness.

This is intentionally structural: it verifies interpretation, local focusing,
causal-boundary, compactness-payment, global authority, contradiction, theorem
boundary, and regression surfaces. It does not certify continuum theorems or
Agda kernel acceptance.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

INTRINSIC = ROOT / "DASHI/Physics/Gravity/IntrinsicSpacetimeCurvatureInterpretationExact.agda"
CAUSAL = ROOT / "DASHI/Physics/Gravity/CausalFutureHorismosNullGeneratorExact.agda"
FOCUSING = ROOT / "DASHI/Physics/Gravity/NullRaychaudhuriSachsFocusingExact.agda"
COMPACTNESS = ROOT / "DASHI/Physics/Gravity/PenroseHorismosCompactnessPaymentExact.agda"
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

require(INTRINSIC, [
    "rubberSheetEmbeddingIsNotIntrinsicLorentzianCurvature",
    "externalDownwardGravityIsNotGRSourceMechanism",
    "extraSpatialEmbeddingDimensionNotRequired",
    "spatialCurvatureIsNotFullSpacetimeCurvature",
    "freeFallUsesTimelikeGeodesicLimit",
    "weakFieldTemporalMetricContribution",
    "timeCurvesIntoSpacePhraseIsNotInvariantGRStatement",
])

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

require(FOCUSING, [
    "Raychaudhuri1955SourceReceipt",
    "Sachs1961SourceReceipt",
    "nullRaychaudhuriEquationTarget",
    "hypersurfaceOrthogonalTwistVanishes",
    "nullConvergenceAndShearForceNonIncreasingExpansion",
    "negativeExpansionForcesFiniteAffineFocusing",
    "trappedSurfaceMeansBothFutureNullExpansionsNegative",
    "localFocusingDoesNotEqualGlobalGeodesicIncompleteness",
    "nullEnergyConditionIsNotNullConvergenceWithoutEinsteinEquation",
    "conjugatePointIsNotSpacetimeSingularity",
    "focusingOwnerInternallyDerivesContinuumEquation",
])

require(COMPACTNESS, [
    "compactTrappedSurfaceCarrier",
    "compactnessPaysUniformNegativeExpansionMargin",
    "uniformAffineFocusingBound",
    "futureNullNormalDirectionFibreCompact",
    "rawNullNormalVectorFibreIsNotCompactDirectionFibre",
    "boundedGeneratorParameterDomainCompact",
    "nullExponentialGeneratorMapContinuous",
    "futureHorismosCoveredByBoundedGeneratorImage",
    "futureHorismosClosedUnderGlobalHyperbolicity",
    "compactnessOwnerInternallyReprovesContinuumTopology",
])

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
    "futureHorismosOfTrappedSurface",
    "sameHorismosObjectCarriesBothReductioClaims",
    "horismosCompactnessConsumer",
    "globalCausalityAuthorityConsumer",
    "nullCompletenessPlusFocusingMakesFutureHorismosCompact",
    "globalHyperbolicityIdentifiesHorismosWithAchronalBoundary",
    "nonCompactCauchySurfaceForcesFutureHorismosNonCompact",
    "compactAndNonCompactHorismosContradiction",
    "globalContradictionForcesNullIncompleteness",
    "globalOwnerInternallyReprovesContinuumCausality",
])

require(PENROSE, [
    "Penrose1965SourceReceipt",
    "nonCompactCauchyHypersurfaceHypothesis",
    "closedTrappedSurfaceHypothesis",
    "nullConvergenceHypothesis",
    "nullGeodesicIncompletenessConclusion",
    "geodesicIncompletenessIsNotSingularPointInSpacetime",
    "incompletenessDoesNotRequireCurvatureScalarDivergence",
    "theoremBoundaryDoesNotProveQuantumGravity",
    "citationImportsNeitherProofNorAuthority",
])

require(REGRESSION, [
    "rubberSheetFirewallRegression",
    "temporalPhraseFirewallRegression",
    "incompletenessPointFirewallRegression",
    "curvatureDivergenceFirewallRegression",
    "causalVsChronologicalFutureFirewallRegression",
    "horismosNotEventHorizonRegression",
    "causalBoundaryDerivationStillClosedRegression",
    "localFocusingNotGlobalIncompletenessRegression",
    "energyConditionTranslationFirewallRegression",
    "focusingContinuumDerivationStillClosedRegression",
    "pointwiseNegativeNotUniformRegression",
    "rawNullVectorFibreFirewallRegression",
    "boundedParameterNotCompactnessRegression",
    "compactnessTopologyDerivationStillClosedRegression",
    "globalAuthorityCitationNonPromotionRegression",
    "globalAuthorityDerivationStillClosedRegression",
    "compactHorismosNotSingularityRegression",
    "nonCompactCauchyIsGlobalInputRegression",
    "globalCausalityDerivationStillClosedRegression",
    "continuumPromotionStillClosedRegression",
])

require(AGGREGATE, [
    "IntrinsicSpacetimeCurvatureInterpretationExact",
    "CausalFutureHorismosNullGeneratorExact",
    "NullRaychaudhuriSachsFocusingExact",
    "PenroseHorismosCompactnessPaymentExact",
    "PenroseGlobalCausalityAuthorityExact",
    "PenroseGlobalHorismosContradictionExact",
    "Penrose1965NullGeodesicIncompletenessExact",
    "IntrinsicPenroseInterpretationRegression",
])

print("GR intrinsic / causal-boundary / compactness / global-authority / Penrose static contract: OK")
