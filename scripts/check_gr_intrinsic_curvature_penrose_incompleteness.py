#!/usr/bin/env python3
"""Focused static contract for intrinsic GR, null focusing, and Penrose incompleteness.

This is intentionally structural: it verifies thin interpretation, local
focusing, global causal/topological, and theorem-boundary owners plus focused
regressions. It does not certify the continuum equations or Penrose theorem.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

INTRINSIC = ROOT / "DASHI/Physics/Gravity/IntrinsicSpacetimeCurvatureInterpretationExact.agda"
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
        raise SystemExit(
            f"{path.relative_to(ROOT)} missing required surfaces: {missing}"
        )


require(
    INTRINSIC,
    [
        "rubberSheetEmbeddingIsNotIntrinsicLorentzianCurvature",
        "externalDownwardGravityIsNotGRSourceMechanism",
        "extraSpatialEmbeddingDimensionNotRequired",
        "spatialCurvatureIsNotFullSpacetimeCurvature",
        "freeFallUsesTimelikeGeodesicLimit",
        "weakFieldTemporalMetricContribution",
        "timeCurvesIntoSpacePhraseIsNotInvariantGRStatement",
    ],
)

require(
    FOCUSING,
    [
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
    ],
)

require(
    GLOBAL,
    [
        "futureHorismosOfTrappedSurface",
        "nullCompletenessPlusFocusingMakesFutureHorismosCompact",
        "globalHyperbolicityIdentifiesHorismosWithAchronalBoundary",
        "nonCompactCauchySurfaceForcesFutureHorismosNonCompact",
        "compactAndNonCompactHorismosContradiction",
        "globalContradictionForcesNullIncompleteness",
        "compactHorismosIsNotSpacetimeSingularity",
        "globalHyperbolicityIsNotMerelyNoClosedTimelikeCurves",
        "nonCompactCauchyIsTopologicalGlobalInputNotLocalCurvature",
        "globalOwnerInternallyReprovesContinuumCausality",
    ],
)

require(
    PENROSE,
    [
        "Penrose1965SourceReceipt",
        "nonCompactCauchyHypersurfaceHypothesis",
        "closedTrappedSurfaceHypothesis",
        "nullConvergenceHypothesis",
        "nullGeodesicIncompletenessConclusion",
        "geodesicIncompletenessIsNotSingularPointInSpacetime",
        "incompletenessDoesNotRequireCurvatureScalarDivergence",
        "theoremBoundaryDoesNotProveQuantumGravity",
        "citationImportsNeitherProofNorAuthority",
    ],
)

require(
    REGRESSION,
    [
        "rubberSheetFirewallRegression",
        "temporalPhraseFirewallRegression",
        "incompletenessPointFirewallRegression",
        "curvatureDivergenceFirewallRegression",
        "localFocusingNotGlobalIncompletenessRegression",
        "energyConditionTranslationFirewallRegression",
        "focusingContinuumDerivationStillClosedRegression",
        "compactHorismosNotSingularityRegression",
        "nonCompactCauchyIsGlobalInputRegression",
        "globalCausalityDerivationStillClosedRegression",
        "continuumPromotionStillClosedRegression",
    ],
)

require(
    AGGREGATE,
    [
        "IntrinsicSpacetimeCurvatureInterpretationExact",
        "NullRaychaudhuriSachsFocusingExact",
        "PenroseGlobalHorismosContradictionExact",
        "Penrose1965NullGeodesicIncompletenessExact",
        "IntrinsicPenroseInterpretationRegression",
    ],
)

print("GR intrinsic-curvature / focusing / global Penrose incompleteness static contract: OK")
