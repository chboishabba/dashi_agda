module DASHI.Governance.AnomalousTemporalCalibratedHypothesisForestExact where

open import DASHI.Core.Prelude

import DASHI.Core.CalibratedExperimentInferenceExact as Calibrated
import DASHI.Core.ReopenableHypothesisForestExact as Forest
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal
import DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact as Trajectory

------------------------------------------------------------------------
-- CALIBRATED INFERENCE OVER THE SAME TEMPORAL FIBRE
--
-- The temporal compatibility predicate is reused literally as the calibrated
-- experiment family's deterministic admissibility relation.  No posterior or
-- confidence semantics are silently added.
------------------------------------------------------------------------

data UnitState : Set where unitState : UnitState
data UnitControl : Set where unitControl : UnitControl
data UnitObservation : Set where unitObservation : UnitObservation
data UnitPrediction : Set where unitPrediction : UnitPrediction
data UnitRisk : Set where unitRisk : UnitRisk

experimentFamily : Calibrated.ExperimentFamily
experimentFamily = Calibrated.experimentFamily
  UnitState
  Trajectory.Interpretation
  UnitControl
  UnitObservation
  UnitPrediction
  UnitRisk
  Trajectory.EvidenceMoment
  (λ _ _ → unitState)
  (λ _ → unitObservation)
  (λ _ → unitPrediction)
  (λ _ → unitRisk)
  Trajectory.Compatible

fibreRefinementToDataRefinement :
  ∀ {before after} →
  Temporal.FibreRefinement Trajectory.temporalSystem before after →
  Calibrated.DataRefinement experimentFamily
fibreRefinementToDataRefinement {before} {after} refinement =
  Calibrated.dataRefinement
    after
    before
    (Temporal.FibreRefinement.retainedWasPreviouslyLive refinement)

bemCalibratedRefinement : Calibrated.DataRefinement experimentFamily
bemCalibratedRefinement =
  fibreRefinementToDataRefinement
    (Temporal.StrictFibreRefinement.refinement
      Trajectory.bemReplicationStrictlyRemovesRobustOriginalEffect)

psilocybinCalibratedRefinement : Calibrated.DataRefinement experimentFamily
psilocybinCalibratedRefinement =
  fibreRefinementToDataRefinement
    (Temporal.StrictFibreRefinement.refinement
      Trajectory.psilocybinMetaEvidenceRemovesPureNoEffectInterpretation)

------------------------------------------------------------------------
-- REOPENABLE HYPOTHESIS FOREST
--
-- An interpretation excluded from the selected current evidence fibre is not
-- automatically an ontological refutation.  Refutation requires a distinct
-- domain witness; this owner intentionally supplies none.
------------------------------------------------------------------------

data NoRefutation : Set where

ReopeningEvidence :
  Forest.DormancyReason → Trajectory.Interpretation → Set
ReopeningEvidence _ interpretation =
  Σ Trajectory.EvidenceMoment λ moment →
    Trajectory.Compatible moment interpretation

hypothesisSemantics : Forest.HypothesisSemantics Trajectory.Interpretation
hypothesisSemantics = Forest.hypothesisSemantics
  (λ _ → NoRefutation)
  ReopeningEvidence

-- The robust original Bem interpretation is excluded at the 2025 slice, but
-- we retain it as reopenable/fidelity-pending rather than claiming a theorem of
-- metaphysical impossibility.
bemRobustOriginalDormant :
  Forest.HypothesisEntry Trajectory.Interpretation Nat
bemRobustOriginalDormant = Forest.hypothesisEntry
  Trajectory.robustBemPrecognition
  (Forest.reopenable Forest.fidelityPending)
  0

-- Its historical 2011 compatibility is enough to witness that it is a real
-- retained historical branch capable of reopening under a future evidential
-- model; this does not say such reopening is scientifically expected.
bemHistoricalReopeningEvidence :
  ReopeningEvidence Forest.fidelityPending Trajectory.robustBemPrecognition
bemHistoricalReopeningEvidence = Trajectory.bemInitial2011 , tt

bemMayReopenFromDormant :
  Forest.HypothesisTransition
    hypothesisSemantics
    Trajectory.robustBemPrecognition
    (Forest.reopenable Forest.fidelityPending)
    Forest.active
bemMayReopenFromDormant =
  Forest.reopen Forest.fidelityPending bemHistoricalReopeningEvidence

-- The pure-no-therapeutic-effect psilocybin interpretation is similarly no
-- longer live in the selected 2025/26 fibre, but exclusion is not itself an
-- ontology theorem.
psilocybinNoEffectDormant :
  Forest.HypothesisEntry Trajectory.Interpretation Nat
psilocybinNoEffectDormant = Forest.hypothesisEntry
  Trajectory.noPsilocybinTherapeuticEffect
  (Forest.reopenable Forest.dependencyChanged)
  0

psilocybinHistoricalReopeningEvidence :
  ReopeningEvidence Forest.dependencyChanged Trajectory.noPsilocybinTherapeuticEffect
psilocybinHistoricalReopeningEvidence = Trajectory.psilocybinEarlyModernTrials , tt

------------------------------------------------------------------------
-- No dormant branch can become refuted merely by pruning it from the current
-- frontier.
------------------------------------------------------------------------

bemDormancyCannotDirectlyBecomeRefutation :
  Forest.HypothesisTransition
    hypothesisSemantics
    Trajectory.robustBemPrecognition
    (Forest.reopenable Forest.fidelityPending)
    Forest.refuted → ⊥
bemDormancyCannotDirectlyBecomeRefutation = Forest.noDirectDormantRefutation

psilocybinDormancyCannotDirectlyBecomeRefutation :
  Forest.HypothesisTransition
    hypothesisSemantics
    Trajectory.noPsilocybinTherapeuticEffect
    (Forest.reopenable Forest.dependencyChanged)
    Forest.refuted → ⊥
psilocybinDormancyCannotDirectlyBecomeRefutation = Forest.noDirectDormantRefutation

------------------------------------------------------------------------
-- Calibration boundaries.
------------------------------------------------------------------------

calibratedBoundary : Calibrated.CalibratedExperimentBoundary
calibratedBoundary = Calibrated.canonicalCalibratedExperimentBoundary

forestBoundary : Forest.ReopenableHypothesisBoundary
forestBoundary = Forest.canonicalReopenableHypothesisBoundary

data FibreExclusionPromotesGlobalRefutation : Set where

data DeterministicCompatibilityPromotesPosteriorProbability : Set where

data RestoredFitPromotesIndependentSupport : Set where

data HistoricalReopeningPromotesCurrentScientificPlausibility : Set where

fibreExclusionDoesNotPromoteGlobalRefutation : FibreExclusionPromotesGlobalRefutation → ⊥
fibreExclusionDoesNotPromoteGlobalRefutation ()

deterministicCompatibilityDoesNotPromotePosteriorProbability :
  DeterministicCompatibilityPromotesPosteriorProbability → ⊥
deterministicCompatibilityDoesNotPromotePosteriorProbability ()

restoredFitDoesNotPromoteIndependentSupport : RestoredFitPromotesIndependentSupport → ⊥
restoredFitDoesNotPromoteIndependentSupport ()

historicalReopeningDoesNotPromoteCurrentPlausibility :
  HistoricalReopeningPromotesCurrentScientificPlausibility → ⊥
historicalReopeningDoesNotPromoteCurrentPlausibility ()

record AnomalousTemporalCalibratedForestBoundary : Set where
  constructor anomalousTemporalCalibratedForestBoundary
  field
    temporalCompatibilityReusesDeterministicAdmissibility : Bool
    temporalCompatibilityReusesDeterministicAdmissibilityIsTrue :
      temporalCompatibilityReusesDeterministicAdmissibility ≡ true
    exclusionFromCurrentFibreEqualsRefutation : Bool
    exclusionFromCurrentFibreEqualsRefutationIsFalse :
      exclusionFromCurrentFibreEqualsRefutation ≡ false
    dormantBranchCanReopenWithExplicitEvidence : Bool
    dormantBranchCanReopenWithExplicitEvidenceIsTrue :
      dormantBranchCanReopenWithExplicitEvidence ≡ true
    deterministicAdmissibilityEqualsPosteriorSupport : Bool
    deterministicAdmissibilityEqualsPosteriorSupportIsFalse :
      deterministicAdmissibilityEqualsPosteriorSupport ≡ false

canonicalAnomalousTemporalCalibratedForestBoundary :
  AnomalousTemporalCalibratedForestBoundary
canonicalAnomalousTemporalCalibratedForestBoundary =
  anomalousTemporalCalibratedForestBoundary
    true refl false refl true refl false refl
