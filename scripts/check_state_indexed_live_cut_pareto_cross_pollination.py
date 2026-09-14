#!/usr/bin/env python3
"""Static contract for state-indexed live-cut Pareto cross-pollination.

The child composes residual/live-set salience, residual-conditioned experiment
portfolios, source-correct SensibLaw guarded cuts, the canonical NS R486/R423
frontier, and least-privilege proof search. It must not create authority, route
around unpaid consumers, or let superseded producer archaeology override the
current canonical terminal cut.
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
    "NSTriadKNCanonicalClayProofSearchRound486Exact",
    "ClayCrossDomainLiteralFrontierExact",
    "StateIndexedLiveCutParetoAdapter",
    "canonicalStateIndexedLiveCutParetoAdapter",
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
    "NSCanonicalCurrentCutParetoAdapter",
    "canonicalNSCanonicalCurrentCutParetoAdapter",
    "nsCurrentResidualIsDirectR423Budget",
    "canonicalShortestConsumerIsR423",
    "directR423BudgetPaid",
    "crossOutputCoherenceRequired",
    "r284DecompositionMandatory",
    "clayPromotionPaid",
    "staleRound83SnapshotMayOverrideCanonicalCut",
    "optionalProducerMayBecomeMandatoryWithoutFrontierImprovement",
    "crossDomainSchedulerShapeProvesSharedMathematics",
    "LeastPrivilegeLiveCutAdmissionAdapter",
    "canonicalLeastPrivilegeLiveCutAdmissionAdapter",
    "liveCutSalienceCannotBypassRouteAdmission",
])

require(REGRESSION, [
    "salienceIsLiveSetIndexedRegression",
    "magnitudeGreedyCanMissNarrowingRegression",
    "salienceNoAdmissionRegression",
    "residualUpdateChangesSelectionRegression",
    "portfolioNoExecutionAuthorityRegression",
    "initialPortfolioCandidateEligibleRegression",
    "laterPortfolioCandidateEligibleRegression",
    "eligibilityNoRouteAdmissionRegression",
    "admittedCandidateEligibilityProjectionRegression",
    "admittedCandidateNoAutomaticParetoRegression",
    "admittedCandidateNoAutomaticTerminalClosureRegression",
    "nsCanonicalResidualRegression",
    "nsCanonicalR423ShortestRegression",
    "nsDirectR423StillOpenRegression",
    "nsCrossOutputNotRequiredRegression",
    "nsR284NotMandatoryRegression",
    "nsClayPromotionStillFalseRegression",
    "nsRound83CannotOverrideCanonicalCutRegression",
    "nsOptionalProducerCannotSelfPromoteRegression",
    "crossDomainShapeNoSharedMathematicsRegression",
    "routeAdmissionRequiredRegression",
    "silentStrengtheningBlockedRegression",
    "localLemmaNoAutomaticFrontierRegression",
    "lemmaCountNoAuthorityRegression",
    "duplicateRouteReuseRegression",
    "liveCutCannotBypassAdmissionRegression",
])

print("State-indexed live-cut Pareto cross-pollination static contract: OK")
