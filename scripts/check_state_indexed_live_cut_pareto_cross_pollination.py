#!/usr/bin/env python3
"""Static contract for state-indexed live-cut Pareto cross-pollination.

The child composes the existing local/global bridge with residual/live-set
salience, residual-conditioned experiment portfolios, source-correct SensibLaw
guarded cuts, the current NS Round83 producer cut, and least-privilege proof
search. It must not create authority or route around unpaid consumers.
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
    "AdmissibleConsumerMDLHyperfabricExact",
    "ActionabilityCostedExperimentChoiceExact",
    "ProofSearchLeastPrivilegeAdmissionExact",
    "SensibLawDutySourceLineageRefinementCutRerunExact",
    "NSTriadKNHighestAlphaRound83Exact",
    "StateIndexedLiveCutParetoAdapter",
    "canonicalStateIndexedLiveCutParetoAdapter",
    "salienceIndexedByResidualAndLiveSet",
    "magnitudeGreedyMayMissLiveNarrowing",
    "salienceCreatesCandidateAdmission",
    "residualUpdateMayChangeSelectedExperiment",
    "portfolioSelectionCreatesExecutionAuthority",
    "terminalConsumerStillRequired",
    "sameGraphFactAppendMayChangeReachabilityAndCut",
    "asStateIndexedMDLProblem",
    "portfolioCandidateIsEligible",
    "stateIndexedEligibilityDoesNotCreateRouteAdmission",
    "AdmittedStateIndexedCandidate",
    "admittedStateIndexedCandidateEligible",
    "admittedCandidateAutomaticallyParetoOptimal",
    "admittedCandidateAutomaticallyClosesTerminalConsumer",
    "GuardedCutAuthorityPromotion",
    "guardedCutCannotPromoteAuthority",
    "OpenCullenRouteTransfersToClimate",
    "openCullenRouteStillDoesNotTransfer",
    "stateIndexedSelectionDoesNotCreateSourceAuthority",
    "historicalEvidenceMayRemainValidWhileNextStepSalienceChanges",
    "NSCurrentCutParetoAdapter",
    "canonicalNSCurrentCutParetoAdapter",
    "relativeGrowthSplitClosed",
    "nonlinearPressureRelativeGrowthEstimatePaid",
    "criticalRatioBarrierPaid",
    "clayPromotionPaid",
    "closedAlgebraRemainsHighestSalience",
    "currentNSCutMayBeSkippedByPareto",
    "crossPollinationCreatesNSTheoremAuthority",
    "LeastPrivilegeLiveCutAdmissionAdapter",
    "canonicalLeastPrivilegeLiveCutAdmissionAdapter",
    "theoremNameStringCreatesProofCapability",
    "routeMayElaborateBeforeAdmission",
    "routeMaySilentlyStrengthenHypotheses",
    "localLemmaAutomaticallyMovesProgrammeFrontier",
    "lemmaCountIsAuthoritativeProgress",
    "duplicateRouteShouldBeReproved",
    "liveCutSalienceCannotBypassRouteAdmission",
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
    "initialPortfolioCandidateEligibleRegression",
    "laterPortfolioCandidateEligibleRegression",
    "eligibilityNoRouteAdmissionRegression",
    "admittedInitialCandidateEligibleRegression",
    "admittedCandidateNoAutomaticParetoRegression",
    "admittedCandidateNoAutomaticTerminalClosureRegression",
    "nsRelativeGrowthSplitClosedRegression",
    "nsPressureProducerStillOpenRegression",
    "nsCriticalBarrierStillOpenRegression",
    "nsClayPromotionStillFalseRegression",
    "nsClosedAlgebraNotHighestSalienceRegression",
    "nsParetoCannotSkipCurrentCutRegression",
    "nsCrossPollinationNoAuthorityRegression",
    "routeAdmissionRequiredRegression",
    "silentStrengtheningBlockedRegression",
    "localLemmaNoAutomaticFrontierRegression",
    "lemmaCountNoAuthorityRegression",
    "duplicateRouteReuseRegression",
    "liveCutCannotBypassAdmissionRegression",
])

print("State-indexed live-cut Pareto cross-pollination static contract: OK")
