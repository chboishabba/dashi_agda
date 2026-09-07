module DASHI.Core.DependencyWeightedDiagnosisSchedulerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis

------------------------------------------------------------------------
-- DEPENDENCY-WEIGHTED DIAGNOSIS SCHEDULER
--
-- Salience says whether a debugging observation shrinks the live diagnosis
-- fibre.  Dependency priority is a separate declared coordinate describing how
-- consequential it is to resolve a diagnosis for the current consumer/graph.
-- Neither priority nor signal magnitude is promoted to truth probability.
------------------------------------------------------------------------

record DependencyPriorityPolicy : Set₁ where
  constructor dependency-priority-policy
  field
    priority : Outcome.OutcomeDiagnosis → Nat
    policyReference : String

open DependencyPriorityPolicy public

record WeightedDebugCandidate
    (policy : DependencyPriorityPolicy)
    (prior : Diagnosis.DiagnosisFibre) : Set₁ where
  constructor weighted-debug-candidate
  field
    observation : Diagnosis.DebugObservation
    narrowing : Diagnosis.DiagnosisSalientOn observation prior
    targetedDiagnosis : Outcome.OutcomeDiagnosis
    targetedWasLive : prior targetedDiagnosis
    targetedEliminated :
      ¬ (Diagnosis.updateDiagnosisFibre observation prior targetedDiagnosis)
    dependencyWeight : Nat
    dependencyWeightCorrect :
      dependencyWeight ≡ priority policy targetedDiagnosis
    candidateReference : String

open WeightedDebugCandidate public

record AtLeastAsHighPriority
    {policy prior}
    (left right : WeightedDebugCandidate policy prior) : Set where
  constructor at-least-as-high-priority
  field
    priorityOrder : dependencyWeight right ≤ dependencyWeight left

open AtLeastAsHighPriority public

------------------------------------------------------------------------
-- Exact calibration: frame conflict is high-priority for this consumer while
-- model conflict is lower-priority.  Both can be separated by magnitude-1
-- controls; the scheduler chooses by declared dependency priority, not signal.
------------------------------------------------------------------------

canonicalPriorityPolicy : DependencyPriorityPolicy
canonicalPriorityPolicy =
  dependency-priority-policy priorityFor
    "synthetic current-consumer dependency priority; not confidence or truth weight"
  where
    priorityFor : Outcome.OutcomeDiagnosis → Nat
    priorityFor Outcome.frameConflict = 5
    priorityFor Outcome.modelConflict = 1
    priorityFor Outcome.premiseConflict = 2
    priorityFor Outcome.observationConflict = 3
    priorityFor Outcome.ruleConflict = 2
    priorityFor Outcome.consumerMismatch = 4
    priorityFor Outcome.provenanceConflict = 4
    priorityFor Outcome.authorityMismatch = 4
    priorityFor Outcome.insufficientResolution = 3

smallModelCheck : Diagnosis.DebugObservation
smallModelCheck =
  Diagnosis.debug-observation
    "small model perturbation/control"
    1
    posterior
    "synthetic debugging calibration: model control eliminates model-conflict branch"
  where
    posterior : Diagnosis.DiagnosisFibre → Diagnosis.DiagnosisFibre
    posterior live Outcome.modelConflict = ⊥
    posterior live diagnosis = live diagnosis

smallModelCheckIsSalient :
  Diagnosis.DiagnosisSalientOn smallModelCheck Diagnosis.ambiguousDiagnosisFibre
smallModelCheckIsSalient =
  Diagnosis.strict-diagnosis-narrowing
    refine
    (Outcome.modelConflict , (tt , (λ x → x)))
  where
    refine :
      ∀ diagnosis →
      Diagnosis.updateDiagnosisFibre smallModelCheck Diagnosis.ambiguousDiagnosisFibre diagnosis →
      Diagnosis.ambiguousDiagnosisFibre diagnosis
    refine Outcome.modelConflict ()
    refine diagnosis proof = proof

frameWeightedCandidate :
  WeightedDebugCandidate canonicalPriorityPolicy Diagnosis.ambiguousDiagnosisFibre
frameWeightedCandidate =
  weighted-debug-candidate
    Diagnosis.smallFrameCheck
    Diagnosis.smallFrameCheckIsSalient
    Outcome.frameConflict
    tt
    (λ x → x)
    5 refl
    "frame control eliminates current high-priority frame diagnosis"

modelWeightedCandidate :
  WeightedDebugCandidate canonicalPriorityPolicy Diagnosis.ambiguousDiagnosisFibre
modelWeightedCandidate =
  weighted-debug-candidate
    smallModelCheck
    smallModelCheckIsSalient
    Outcome.modelConflict
    tt
    (λ x → x)
    1 refl
    "model control eliminates current lower-priority model diagnosis"

frameCandidateAtLeastAsHighPriorityAsModel :
  AtLeastAsHighPriority frameWeightedCandidate modelWeightedCandidate
frameCandidateAtLeastAsHighPriorityAsModel =
  at-least-as-high-priority (s≤s z≤n)

bothDebugSignalsHaveMagnitudeOne :
  Diagnosis.magnitude (observation frameWeightedCandidate)
  ≡ Diagnosis.magnitude (observation modelWeightedCandidate)
bothDebugSignalsHaveMagnitudeOne = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DependencyPriorityIsTruthProbability : Set where
data HigherPriorityMeansDiagnosisTrue : Set where
data HigherSignalMagnitudeMeansHigherDependencyPriority : Set where

dependencyPriorityIsNotTruthProbability :
  DependencyPriorityIsTruthProbability → ⊥
dependencyPriorityIsNotTruthProbability ()

higherPriorityDoesNotMeanDiagnosisTrue : HigherPriorityMeansDiagnosisTrue → ⊥
higherPriorityDoesNotMeanDiagnosisTrue ()

signalMagnitudeDoesNotSetDependencyPriority :
  HigherSignalMagnitudeMeansHigherDependencyPriority → ⊥
signalMagnitudeDoesNotSetDependencyPriority ()

record DependencyWeightedDiagnosisBoundary : Set where
  constructor dependency-weighted-diagnosis-boundary
  field
    priorityIsConsumerGraphRelative : Bool
    prioritySeparateFromSignalMagnitude : Bool
    prioritySeparateFromTruthProbability : Bool
    equalMagnitudeMovesMayHaveDifferentPriority : Bool
    weightedSchedulerCreatesAuthority : Bool

canonicalDependencyWeightedDiagnosisBoundary : DependencyWeightedDiagnosisBoundary
canonicalDependencyWeightedDiagnosisBoundary =
  dependency-weighted-diagnosis-boundary true true true true false
