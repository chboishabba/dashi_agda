#!/usr/bin/env python3
"""Static contract for state-indexed live-cut Pareto cross-pollination.

The child composes residual/live-set salience, residual-conditioned experiment
portfolios, source-correct guarded cuts, canonical Clay frontiers, literal
frontier dispositions, and least-privilege proof search. It must not fabricate
Pareto costs from labels or route around unpaid consumers.
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
    "DiscriminatorSynthesisExact",
    "ProofSearchLeastPrivilegeAdmissionExact",
    "LiteralFrontierSchedulerExact",
    "NSYMLiteralFrontierSchedulerExact",
    "BalabanActiveSourceDiscriminator2026Exact",
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
    "LeastPrivilegeLiveCutAdmissionAdapter",
    "canonicalLeastPrivilegeLiveCutAdmissionAdapter",
    "liveCutSalienceCannotBypassRouteAdmission",
    "LiteralFrontierParetoBoundaryAdapter",
    "canonicalLiteralFrontierParetoBoundaryAdapter",
    "paretoReferenceConstructsCostHyperfabric",
    "ymDirectRouteStillConjunctive",
    "YMNumericalDirectClosure",
    "ymNumericalCannotCloseLeaf",
    "ymQuantitativeParetoRankingAvailableWithoutDeclaredCosts",
    "YMSourceRecoveryConsumerAdapter",
    "canonicalYMSourceRecoveryConsumerAdapter",
    "ymLiteralRecoveryProbeCostIsOne",
    "ymLiteralProbeClosesRecoveryDecision",
    "matchingSourceLabelsCloseLiteralRecovery",
    "machineCheckedCompilerImpliesLiteralSourceInhabitation",
    "declaredProbeCostCreatesRouteAdmission",
    "consumerClosingProbeClosesYMTheoremLeaf",
])

require(REGRESSION, [
    "initialPortfolioCandidateEligibleRegression",
    "laterPortfolioCandidateEligibleRegression",
    "eligibilityNoRouteAdmissionRegression",
    "admittedCandidateEligibilityProjectionRegression",
    "admittedCandidateNoAutomaticParetoRegression",
    "admittedCandidateNoAutomaticTerminalClosureRegression",
    "nsCanonicalResidualRegression",
    "nsDirectR423StillOpenRegression",
    "literalParetoReferenceNoCostHyperfabricRegression",
    "ymDirectRouteConjunctiveRegression",
    "ymNumericalNoDirectClosureRegression",
    "ymNoQuantitativeParetoWithoutCostsRegression",
    "ymSourceProbeCostRegression",
    "ymSourceProbeConsumerClosureRegression",
    "ymLabelsNoClosureRegression",
    "ymCompilerNoLiteralSourceInhabitationRegression",
    "ymProbeCostNoRouteAdmissionRegression",
    "ymProbeNoTheoremLeafClosureRegression",
    "routeAdmissionRequiredRegression",
    "silentStrengtheningBlockedRegression",
    "localLemmaNoAutomaticFrontierRegression",
    "lemmaCountNoAuthorityRegression",
    "duplicateRouteReuseRegression",
    "liveCutCannotBypassAdmissionRegression",
])

print("State-indexed live-cut Pareto cross-pollination static contract: OK")
