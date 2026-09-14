module DASHI.Interop.StateIndexedLiveCutParetoCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.PenroseLocalGlobalHyperfabricCrossPollinationExact as Parent
import DASHI.Core.ResidualLiveSetSalienceSchedulerBidiExact as Live
import DASHI.Core.ResidualConditionedExperimentPortfolioExact as Portfolio
import DASHI.Cognition.PNF.SensibLawDutySourceLineageRefinementCutRerunExact as GuardedCut

------------------------------------------------------------------------
-- STATE-INDEXED LIVE-CUT / PARETO CHILD
--
-- Parent pattern:
--   candidate -> compatibility/admission -> terminal consumer -> Pareto.
--
-- This child adds state dependence. The live hypothesis/residual/cut state is
-- recomputed first; only moves that remain relevant to that state are eligible
-- for subsequent authority/consumer gates and Pareto comparison.
--
-- The SensibLaw donor is source-correct and domain-specific. We reuse its exact
-- same-graph refinement/cut behaviour and its non-promotion firewalls without
-- treating the legal theorem as a generic scientific theorem or vice versa.
------------------------------------------------------------------------

record StateIndexedLiveCutParetoAdapter : Set where
  constructor stateIndexedLiveCutParetoAdapter
  field
    liveSetReference : String
    residualPortfolioReference : String
    guardedCutReference : String
    paretoReference : String

    salienceIndexedByResidualAndLiveSet : Bool
    salienceIndexedByResidualAndLiveSetIsTrue :
      salienceIndexedByResidualAndLiveSet ≡ true

    magnitudeGreedyMayMissLiveNarrowing : Bool
    magnitudeGreedyMayMissLiveNarrowingIsTrue :
      magnitudeGreedyMayMissLiveNarrowing ≡ true

    salienceCreatesCandidateAdmission : Bool
    salienceCreatesCandidateAdmissionIsFalse :
      salienceCreatesCandidateAdmission ≡ false

    residualUpdateMayChangeSelectedExperiment : Bool
    residualUpdateMayChangeSelectedExperimentIsTrue :
      residualUpdateMayChangeSelectedExperiment ≡ true

    portfolioSelectionCreatesExecutionAuthority : Bool
    portfolioSelectionCreatesExecutionAuthorityIsFalse :
      portfolioSelectionCreatesExecutionAuthority ≡ false

    terminalConsumerStillRequired : Bool
    terminalConsumerStillRequiredIsTrue : terminalConsumerStillRequired ≡ true

    sameGraphFactAppendMayChangeReachabilityAndCut : Bool
    sameGraphFactAppendMayChangeReachabilityAndCutIsTrue :
      sameGraphFactAppendMayChangeReachabilityAndCut ≡ true

    stateIndexedSelectionDoesNotCreateSourceAuthority : Bool
    stateIndexedSelectionDoesNotCreateSourceAuthorityIsTrue :
      stateIndexedSelectionDoesNotCreateSourceAuthority ≡ true

    historicalEvidenceMayRemainValidWhileNextStepSalienceChanges : Bool
    historicalEvidenceMayRemainValidWhileNextStepSalienceChangesIsTrue :
      historicalEvidenceMayRemainValidWhileNextStepSalienceChanges ≡ true

open StateIndexedLiveCutParetoAdapter public

canonicalStateIndexedLiveCutParetoAdapter : StateIndexedLiveCutParetoAdapter
canonicalStateIndexedLiveCutParetoAdapter = stateIndexedLiveCutParetoAdapter
  "ResidualLiveSetSalienceSchedulerBidiExact: salience is strict narrowing of the current live set"
  "ResidualConditionedExperimentPortfolioExact: relevance/admissibility are indexed by current residual, consumer, and authority"
  "SensibLawDutySourceLineageRefinementCutRerunExact: same source-lineage graph, source-owned fact append, recomputed reachability and guarded cut"
  "PenroseLocalGlobalHyperfabricCrossPollinationExact: terminal consumer and hard-gated Pareto selection"
  (Live.salienceIndexedByResidualAndLiveSet Live.canonicalResidualLiveSetSalienceBoundary)
  refl
  (Live.magnitudeGreedyMayMissNarrowing Live.canonicalResidualLiveSetSalienceBoundary)
  refl
  (Live.salienceCreatesCandidateAdmission Live.canonicalResidualLiveSetSalienceBoundary)
  refl
  (Portfolio.residualUpdateMayChangeSelectedExperiment
    Portfolio.canonicalResidualConditionedPortfolioBoundary)
  (Portfolio.residualUpdateMayChangeSelectedExperimentIsTrue
    Portfolio.canonicalResidualConditionedPortfolioBoundary)
  (Portfolio.portfolioSelectionCreatesExecutionAuthority
    Portfolio.canonicalResidualConditionedPortfolioBoundary)
  (Portfolio.portfolioSelectionCreatesExecutionAuthorityIsFalse
    Portfolio.canonicalResidualConditionedPortfolioBoundary)
  Parent.terminalConsumerStillMustBePaid
  Parent.terminalConsumerStillMustBePaidIsTrue
  true refl
  true refl
  true refl

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
-- Parent payment / attribution boundaries remain live in the child.
------------------------------------------------------------------------

parentSnowballPaymentMaySkipDependency : Bool
parentSnowballPaymentMaySkipDependency = Parent.snowballPaymentMaySkipUnpaidParentDependency

parentSnowballPaymentMaySkipDependencyIsFalse :
  parentSnowballPaymentMaySkipDependency ≡ false
parentSnowballPaymentMaySkipDependencyIsFalse =
  Parent.snowballPaymentMaySkipUnpaidParentDependencyIsFalse

parentCrossDomainAnalogyCreatesAuthority : Bool
parentCrossDomainAnalogyCreatesAuthority = Parent.crossDomainAnalogyCreatesSourceAuthority

parentCrossDomainAnalogyCreatesAuthorityIsFalse :
  parentCrossDomainAnalogyCreatesAuthority ≡ false
parentCrossDomainAnalogyCreatesAuthorityIsFalse =
  Parent.crossDomainAnalogyCreatesSourceAuthorityIsFalse

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record StateIndexedLiveCutParetoBoundary : Set where
  constructor stateIndexedLiveCutParetoBoundary
  field
    staleHistoricalEvidenceMustBeDeleted : Bool
    staleHistoricalEvidenceMustBeDeletedIsFalse :
      staleHistoricalEvidenceMustBeDeleted ≡ false
    onceUsefulExperimentAlwaysHighestSalience : Bool
    onceUsefulExperimentAlwaysHighestSalienceIsFalse :
      onceUsefulExperimentAlwaysHighestSalience ≡ false
    currentSalienceAutomaticallyCreatesAuthority : Bool
    currentSalienceAutomaticallyCreatesAuthorityIsFalse :
      currentSalienceAutomaticallyCreatesAuthority ≡ false
    currentMinimalCutAutomaticallyTransfersAcrossDomains : Bool
    currentMinimalCutAutomaticallyTransfersAcrossDomainsIsFalse :
      currentMinimalCutAutomaticallyTransfersAcrossDomains ≡ false
    paretoRankingMayIgnoreCurrentResidualState : Bool
    paretoRankingMayIgnoreCurrentResidualStateIsFalse :
      paretoRankingMayIgnoreCurrentResidualState ≡ false

open StateIndexedLiveCutParetoBoundary public

canonicalStateIndexedLiveCutParetoBoundary : StateIndexedLiveCutParetoBoundary
canonicalStateIndexedLiveCutParetoBoundary = stateIndexedLiveCutParetoBoundary
  false refl
  (Portfolio.onceUsefulExperimentAlwaysHighestSalience
    Portfolio.canonicalResidualConditionedPortfolioBoundary)
  (Portfolio.onceUsefulExperimentAlwaysHighestSalienceIsFalse
    Portfolio.canonicalResidualConditionedPortfolioBoundary)
  false refl
  false refl
  false refl
