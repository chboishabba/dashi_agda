#!/usr/bin/env python3
"""Focused static contract for intrinsic-GR interpretation and Penrose incompleteness.

This is intentionally structural: it verifies that the repo contains a thin
interpretation owner, a theorem-boundary owner, and a focused Agda regression,
with the expected WrongType firewalls exported through the existing physics
aggregate. It does not certify the continuum theorem itself.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

INTRINSIC = ROOT / "DASHI/Physics/Gravity/IntrinsicSpacetimeCurvatureInterpretationExact.agda"
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
        "continuumPromotionStillClosedRegression",
    ],
)

require(
    AGGREGATE,
    [
        "IntrinsicSpacetimeCurvatureInterpretationExact",
        "Penrose1965NullGeodesicIncompletenessExact",
        "IntrinsicPenroseInterpretationRegression",
    ],
)

print("GR intrinsic-curvature / Penrose incompleteness static contract: OK")
