module DASHI.Interop.StateIndexedLiveCutParetoCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.PenroseLocalGlobalHyperfabricCrossPollinationExact as Parent
import DASHI.Core.ResidualLiveSetSalienceSchedulerBidiExact as Live
import DASHI.Core.ResidualConditionedExperimentPortfolioExact as Portfolio
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Cognition.PNF.SensibLawDutySourceLineageRefinementCutRerunExact as GuardedCut
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound83Exact as NS83

------------------------------------------------------------------------
-- STATE-INDEXED LIVE-CUT / PARETO CHILD
------------------------------------------------------------------------

record StateIndexedLiveCutParetoAdapter : Set where
  constructor stateIndexedLiveCutParetoAdapter
  field
    liveSetReference : String
    residualPortfolioReference : String
    guardedCutReference : String
    paretoReference : String
    salienceIndexedByResidualAndLiveSet : Bool
    salienceIndexedByResidualAndLiveSetIsTrue : salienceIndexedByResidualAndLiveSet ≡ true
    magnitudeGreedyMayMissLiveNarrowing : Bool
    magnitudeGreedyMayMissLiveNarrowingIsTrue : magnitudeGreedyMayMissLiveNarrowing ≡ true
    salienceCreatesCandidateAdmission : Bool
    salienceCreatesCandidateAdmissionIsFalse : salienceCreatesCandidateAdmission ≡ false
    residualUpdateMayChangeSelectedExperiment : Bool
    residualUpdateMayChangeSelectedExperimentIsTrue : residualUpdateMayChangeSelectedExperiment ≡ true
    portfolioSelectionCreatesExecutionAuthority : Bool
    portfolioSelectionCreatesExecutionAuthorityIsFalse : portfolioSelectionCreatesExecutionAuthority ≡ false
    terminalConsumerStillRequired : Bool
    terminalConsumerStillRequiredIsTrue : terminalConsumerStillRequired ≡ true
    sameGraphFactAppendMayChangeReachabilityAndCut : Bool
    sameGraphFactAppendMayChangeReachabilityAndCutIsTrue : sameGraphFactAppendMayChangeReachabilityAndCut ≡ true
    stateIndexedSelectionDoesNotCreateSourceAuthority : Bool
    stateIndexedSelectionDoesNotCreateSourceAuthorityIsTrue : stateIndexedSelectionDoesNotCreateSourceAuthority ≡ true
    historicalEvidenceMayRemainValidWhileNextStepSalienceChanges : Bool
    historicalEvidenceMayRemainValidWhileNextStepSalienceChangesIsTrue : historicalEvidenceMayRemainValidWhileNextStepSalienceChanges ≡ true

open StateIndexedLiveCutParetoAdapter public

canonicalStateIndexedLiveCutParetoAdapter : StateIndexedLiveCutParetoAdapter
canonicalStateIndexedLiveCutParetoAdapter = stateIndexedLiveCutParetoAdapter
  "ResidualLiveSetSalienceSchedulerBidiExact: salience is strict narrowing of the current live set"
  "ResidualConditionedExperimentPortfolioExact: relevance/admissibility are indexed by current residual, consumer, and authority"
  "SensibLawDutySourceLineageRefinementCutRerunExact: same source-lineage graph, source-owned fact append, recomputed reachability and guarded cut"
  "PenroseLocalGlobalHyperfabricCrossPollinationExact: terminal consumer and hard-gated Pareto selection"
  (Live.salienceIndexedByResidualAndLiveSet Live.canonicalResidualLiveSetSalienceBoundary) refl
  (Live.magnitudeGreedyMayMissNarrowing Live.canonicalResidualLiveSetSalienceBoundary) refl
  (Live.salienceCreatesCandidateAdmission Live.canonicalResidualLiveSetSalienceBoundary) refl
  (Portfolio.residualUpdateMayChangeSelectedExperiment Portfolio.canonicalResidualConditionedPortfolioBoundary)
  (Portfolio.residualUpdateMayChangeSelectedExperimentIsTrue Portfolio.canonicalResidualConditionedPortfolioBoundary)
  (Portfolio.portfolioSelectionCreatesExecutionAuthority Portfolio.canonicalResidualConditionedPortfolioBoundary)
  (Portfolio.portfolioSelectionCreatesExecutionAuthorityIsFalse Portfolio.canonicalResidualConditionedPortfolioBoundary)
  Parent.terminalConsumerStillMustBePaid Parent.terminalConsumerStillMustBePaidIsTrue
  true refl true refl true refl

------------------------------------------------------------------------
-- Constructive state-indexed Pareto eligibility weld.
------------------------------------------------------------------------

asStateIndexedMDLProblem :
  (P : Portfolio.ExperimentPortfolio) →
  Portfolio.ResidualContext P →
  Portfolio.Consumer P →
  Portfolio.Authority P →
  Pareto.ConsumerMDLProblem
asStateIndexedMDLProblem P residual consumer authority =
  Pareto.consumerMDLProblem
    (Portfolio.Experiment P)
    (λ experiment → Portfolio.admissibleNow P authority experiment ≡ true)
    (λ experiment → Portfolio.relevantNow P residual consumer experiment ≡ true)
    (λ experiment → Choice.cost (Portfolio.move P experiment))
    (λ _ _ → ⊤)
    (Portfolio.experimentReference P)
    "state-indexed residual-portfolio resource-cost code"
    "current residual / consumer / authority context"

portfolioCandidateIsEligible :
  ∀ {P residual consumer authority experiment} →
  Portfolio.PortfolioCandidate P residual consumer authority experiment →
  Pareto.Eligible (asStateIndexedMDLProblem P residual consumer authority) experiment
portfolioCandidateIsEligible candidate = Portfolio.admissible candidate , Portfolio.relevant candidate

stateIndexedEligibilityDoesNotCreateRouteAdmission : Bool
stateIndexedEligibilityDoesNotCreateRouteAdmission = true

stateIndexedEligibilityDoesNotCreateRouteAdmissionIsTrue :
  stateIndexedEligibilityDoesNotCreateRouteAdmission ≡ true
stateIndexedEligibilityDoesNotCreateRouteAdmissionIsTrue = refl

------------------------------------------------------------------------
-- Admitted live-cut candidate: eligibility + independent route admission.
--
-- RouteAdmission is intentionally supplied independently. This record does not
-- manufacture a route-specific receipt from a portfolio candidate. It merely
-- bundles already-paid current-state eligibility with already-paid proof-search
-- admission and retains the terminal-consumer reference that must still close.
------------------------------------------------------------------------

record AdmittedStateIndexedCandidate
    (P : Portfolio.ExperimentPortfolio)
    (residual : Portfolio.ResidualContext P)
    (consumer : Portfolio.Consumer P)
    (authority : Portfolio.Authority P)
    (experiment : Portfolio.Experiment P) : Set where
  constructor admitted-state-indexed-candidate
  field
    currentPortfolioCandidate :
      Portfolio.PortfolioCandidate P residual consumer authority experiment
    routeAdmission : ProofSearch.RouteAdmission
    terminalConsumerReference : String

open AdmittedStateIndexedCandidate public

admittedStateIndexedCandidateEligible :
  ∀ {P residual consumer authority experiment} →
  AdmittedStateIndexedCandidate P residual consumer authority experiment →
  Pareto.Eligible (asStateIndexedMDLProblem P residual consumer authority) experiment
admittedStateIndexedCandidateEligible admitted =
  portfolioCandidateIsEligible (currentPortfolioCandidate admitted)

admittedCandidateAutomaticallyParetoOptimal : Bool
admittedCandidateAutomaticallyParetoOptimal = false

admittedCandidateAutomaticallyParetoOptimalIsFalse :
  admittedCandidateAutomaticallyParetoOptimal ≡ false
admittedCandidateAutomaticallyParetoOptimalIsFalse = refl

admittedCandidateAutomaticallyClosesTerminalConsumer : Bool
admittedCandidateAutomaticallyClosesTerminalConsumer = false

admittedCandidateAutomaticallyClosesTerminalConsumerIsFalse :
  admittedCandidateAutomaticallyClosesTerminalConsumer ≡ false
admittedCandidateAutomaticallyClosesTerminalConsumerIsFalse = refl

------------------------------------------------------------------------
-- Exact source-/authority-preserving legal adapters.
------------------------------------------------------------------------

GuardedCutAuthorityPromotion : Set
GuardedCutAuthorityPromotion = GuardedCut.GuardedCutPromotesReconstructionToRatio

guardedCutCannotPromoteAuthority : GuardedCutAuthorityPromotion → ⊥
guardedCutCannotPromoteAuthority = GuardedCut.cutDoesNotChangeAuthorityRole

OpenCullenRouteTransfersToClimate : Set
OpenCullenRouteTransfersToClimate = GuardedCut.OpenCullenRouteTransfersToClimate

openCullenRouteStillDoesNotTransfer : OpenCullenRouteTransfersToClimate → ⊥
openCullenRouteStillDoesNotTransfer = GuardedCut.specificOpenRouteStillDoesNotTransfer

------------------------------------------------------------------------
-- Current NS producer-cut adapter.
------------------------------------------------------------------------

record NSCurrentCutParetoAdapter : Set where
  constructor nsCurrentCutParetoAdapter
  field
    currentProducerCutReference : String
    sourceCustodyReference : String
    relativeGrowthSplitClosed : Bool
    relativeGrowthSplitClosedIsTrue : relativeGrowthSplitClosed ≡ true
    nonlinearPressureRelativeGrowthEstimatePaid : Bool
    nonlinearPressureRelativeGrowthEstimatePaidIsFalse : nonlinearPressureRelativeGrowthEstimatePaid ≡ false
    criticalRatioBarrierPaid : Bool
    criticalRatioBarrierPaidIsFalse : criticalRatioBarrierPaid ≡ false
    clayPromotionPaid : Bool
    clayPromotionPaidIsFalse : clayPromotionPaid ≡ false
    closedAlgebraRemainsHighestSalience : Bool
    closedAlgebraRemainsHighestSalienceIsFalse : closedAlgebraRemainsHighestSalience ≡ false
    currentNSCutMayBeSkippedByPareto : Bool
    currentNSCutMayBeSkippedByParetoIsFalse : currentNSCutMayBeSkippedByPareto ≡ false
    crossPollinationCreatesNSTheoremAuthority : Bool
    crossPollinationCreatesNSTheoremAuthorityIsFalse : crossPollinationCreatesNSTheoremAuthority ≡ false

open NSCurrentCutParetoAdapter public

canonicalNSCurrentCutParetoAdapter : NSCurrentCutParetoAdapter
canonicalNSCurrentCutParetoAdapter = nsCurrentCutParetoAdapter
  "Round83 live producer: pressure-resolved selected-event geometry -> cutoff-uniform nonlinearRelativeGrowthCore estimate -> viscous combination -> integrated margin -> occupation/replenishment/residence"
  "all analytic/source attribution remains owned by NSTriadKNHighestAlphaRound83Exact and its imported source/theorem owners"
  NS83.round83RelativeGrowthSplitsViscousNonlinearExactly
  NS83.round83RelativeGrowthSplitsViscousNonlinearExactlyIsTrue
  NS83.round83NonlinearPressureRelativeGrowthEstimateConstructed
  NS83.round83NonlinearPressureRelativeGrowthEstimateConstructedIsFalse
  NS83.round83CriticalRatioBarrier refl
  NS83.round83ClayPromotion NS83.round83ClayPromotionIsFalse
  false refl false refl false refl

------------------------------------------------------------------------
-- Least-privilege route admission adapter.
------------------------------------------------------------------------

record LeastPrivilegeLiveCutAdmissionAdapter : Set where
  constructor leastPrivilegeLiveCutAdmissionAdapter
  field
    admissionReference : String
    theoremNameStringCreatesProofCapability : Bool
    theoremNameStringCreatesProofCapabilityIsFalse : theoremNameStringCreatesProofCapability ≡ false
    routeMayElaborateBeforeAdmission : Bool
    routeMayElaborateBeforeAdmissionIsFalse : routeMayElaborateBeforeAdmission ≡ false
    routeMaySilentlyStrengthenHypotheses : Bool
    routeMaySilentlyStrengthenHypothesesIsFalse : routeMaySilentlyStrengthenHypotheses ≡ false
    localLemmaAutomaticallyMovesProgrammeFrontier : Bool
    localLemmaAutomaticallyMovesProgrammeFrontierIsFalse : localLemmaAutomaticallyMovesProgrammeFrontier ≡ false
    lemmaCountIsAuthoritativeProgress : Bool
    lemmaCountIsAuthoritativeProgressIsFalse : lemmaCountIsAuthoritativeProgress ≡ false
    duplicateRouteShouldBeReproved : Bool
    duplicateRouteShouldBeReprovedIsFalse : duplicateRouteShouldBeReproved ≡ false
    liveCutSalienceCannotBypassRouteAdmission : Bool
    liveCutSalienceCannotBypassRouteAdmissionIsTrue : liveCutSalienceCannotBypassRouteAdmission ≡ true

open LeastPrivilegeLiveCutAdmissionAdapter public

canonicalLeastPrivilegeLiveCutAdmissionAdapter : LeastPrivilegeLiveCutAdmissionAdapter
canonicalLeastPrivilegeLiveCutAdmissionAdapter = leastPrivilegeLiveCutAdmissionAdapter
  "current live-cut candidates still require ProofSearch.RouteAdmission before elaboration; salience is not capability"
  (ProofSearch.theoremNameStringIsProofCapability ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.theoremNameStringIsProofCapabilityIsFalse ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.routeMayElaborateBeforeAdmission ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.routeMayElaborateBeforeAdmissionIsFalse ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.routeMaySilentlyStrengthenHypotheses ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.routeMaySilentlyStrengthenHypothesesIsFalse ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.localLemmaAutomaticallyMovesProgrammeFrontier ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.localLemmaAutomaticallyMovesProgrammeFrontierIsFalse ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.lemmaCountIsAuthoritativeProgress ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.lemmaCountIsAuthoritativeProgressIsFalse ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.duplicateRouteShouldBeReproved ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  (ProofSearch.duplicateRouteShouldBeReprovedIsFalse ProofSearch.canonicalProofSearchLeastPrivilegeBoundary)
  true refl

------------------------------------------------------------------------
-- Parent payment / attribution boundaries remain live in the child.
------------------------------------------------------------------------

parentSnowballPaymentMaySkipDependency : Bool
parentSnowballPaymentMaySkipDependency = Parent.snowballPaymentMaySkipUnpaidParentDependency

parentSnowballPaymentMaySkipDependencyIsFalse : parentSnowballPaymentMaySkipDependency ≡ false
parentSnowballPaymentMaySkipDependencyIsFalse = Parent.snowballPaymentMaySkipUnpaidParentDependencyIsFalse

parentCrossDomainAnalogyCreatesAuthority : Bool
parentCrossDomainAnalogyCreatesAuthority = Parent.crossDomainAnalogyCreatesSourceAuthority

parentCrossDomainAnalogyCreatesAuthorityIsFalse : parentCrossDomainAnalogyCreatesAuthority ≡ false
parentCrossDomainAnalogyCreatesAuthorityIsFalse = Parent.crossDomainAnalogyCreatesSourceAuthorityIsFalse

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record StateIndexedLiveCutParetoBoundary : Set where
  constructor stateIndexedLiveCutParetoBoundary
  field
    staleHistoricalEvidenceMustBeDeleted : Bool
    staleHistoricalEvidenceMustBeDeletedIsFalse : staleHistoricalEvidenceMustBeDeleted ≡ false
    onceUsefulExperimentAlwaysHighestSalience : Bool
    onceUsefulExperimentAlwaysHighestSalienceIsFalse : onceUsefulExperimentAlwaysHighestSalience ≡ false
    currentSalienceAutomaticallyCreatesAuthority : Bool
    currentSalienceAutomaticallyCreatesAuthorityIsFalse : currentSalienceAutomaticallyCreatesAuthority ≡ false
    currentMinimalCutAutomaticallyTransfersAcrossDomains : Bool
    currentMinimalCutAutomaticallyTransfersAcrossDomainsIsFalse : currentMinimalCutAutomaticallyTransfersAcrossDomains ≡ false
    paretoRankingMayIgnoreCurrentResidualState : Bool
    paretoRankingMayIgnoreCurrentResidualStateIsFalse : paretoRankingMayIgnoreCurrentResidualState ≡ false

open StateIndexedLiveCutParetoBoundary public

canonicalStateIndexedLiveCutParetoBoundary : StateIndexedLiveCutParetoBoundary
canonicalStateIndexedLiveCutParetoBoundary = stateIndexedLiveCutParetoBoundary
  false refl
  (Portfolio.onceUsefulExperimentAlwaysHighestSalience Portfolio.canonicalResidualConditionedPortfolioBoundary)
  (Portfolio.onceUsefulExperimentAlwaysHighestSalienceIsFalse Portfolio.canonicalResidualConditionedPortfolioBoundary)
  false refl false refl false refl
