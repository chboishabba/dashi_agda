#!/usr/bin/env python3
"""Static contract for state-indexed live-cut Pareto cross-pollination.

The child composes the existing local/global bridge with residual/live-set
salience, residual-conditioned experiment portfolios, and the source-correct
SensibLaw guarded-cut rerun. It must not create legal authority, execution
authority, or candidate admission from salience alone.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Interop/StateIndexedLiveCutParetoCrossPollinationExact.agda"
REGRESSION = ROOT / "DASHI/Interop/StateIndexedLiveCutParetoCrossPollinationRegression.agda"


def require(path: Path, needles: list[str]) -> None:
    if not path.exists():
        raise SystemExit(f"missing required file: {path.relative_to(ROOT)}")
    text = path.read_text(encoding="utf-8")
    missing = [needle for needle in needles if needle not in text]
    if missing:
        raise SystemExit(f"{path.relative_to(ROOT)} missing required surfaces: {missing}")


require(OWNER, [
    "PenroseLocalGlobalHyperfabricCrossPollinationExact",
    "ResidualLiveSetSalienceSchedulerBidiExact",
    "ResidualConditionedExperimentPortfolioExact",
    "SensibLawDutySourceLineageRefinementCutRerunExact",
    "StateIndexedLiveCutParetoAdapter",
    "canonicalStateIndexedLiveCutParetoAdapter",
    "salienceIndexedByResidualAndLiveSet",
    "magnitudeGreedyMayMissLiveNarrowing",
    "salienceCreatesCandidateAdmission",
    "residualUpdateMayChangeSelectedExperiment",
    "portfolioSelectionCreatesExecutionAuthority",
    "terminalConsumerStillRequired",
    "sameGraphFactAppendMayChangeReachabilityAndCut",
    "GuardedCutAuthorityPromotion",
    "guardedCutCannotPromoteAuthority",
    "OpenCullenRouteTransfersToClimate",
    "openCullenRouteStillDoesNotTransfer",
    "stateIndexedSelectionDoesNotCreateSourceAuthority",
    "historicalEvidenceMayRemainValidWhileNextStepSalienceChanges",
])

require(REGRESSION, [
    "salienceIsLiveSetIndexedRegression",
    "magnitudeGreedyCanMissNarrowingRegression",
    "salienceNoAdmissionRegression",
    "residualUpdateChangesSelectionRegression",
    "portfolioNoExecutionAuthorityRegression",
    "terminalConsumerStillRequiredRegression",
    "sameGraphCutStateChangeRegression",
    "stateIndexedSelectionNoSourceAuthorityRegression",
])

print("State-indexed live-cut Pareto cross-pollination static contract: OK")
