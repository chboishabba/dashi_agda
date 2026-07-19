module DASHI.Biology.Levin.FunctionalAgencyRatchet where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate relation between learning performance and higher-level causal
-- integration.  No causal-emergence metric is assumed canonical here.

record NetworkLearningState : Set where
  field
    learningScore      : Nat
    integrationScore   : Nat
    retainedAfterErase : Nat

record FunctionalAgencyRatchetWitness
  (before after erased : NetworkLearningState) : Set where
  field
    trainingImprovesLearning : Bool
    trainingImprovesIntegration : Bool
    erasureReducesTaskMemory : Bool
    erasureRetainsIntegrationGain : Bool
    sameMetricAcrossStates : Bool
    interventionControlled : Bool
    biologicalAndRandomBaselinesCompared : Bool

record RatchetInterpretationBoundary : Set where
  field
    metricChoiceDeclared : Bool
    coarseGrainingDeclared : Bool
    directionOfCausationEstablished : Bool
    randomNetworkBaselineEstablished : Bool
    selectionIndependenceEstablished : Bool
    universalAgencyClaimBlocked : Bool
    interpretation : String

canonicalRatchetInterpretationBoundary : RatchetInterpretationBoundary
canonicalRatchetInterpretationBoundary = record
  { metricChoiceDeclared = true
  ; coarseGrainingDeclared = true
  ; directionOfCausationEstablished = false
  ; randomNetworkBaselineEstablished = false
  ; selectionIndependenceEstablished = false
  ; universalAgencyClaimBlocked = true
  ; interpretation = "Learning-integration feedback is a candidate dynamical ratchet whose status depends on metric, coarse-graining, intervention, and baseline choices"
  }

HigherCausalEmergenceImpliesMind : Bool
HigherCausalEmergenceImpliesMind = false

TrainingRatchetImpliesEvolutionIndependent : Bool
TrainingRatchetImpliesEvolutionIndependent = false

ForgettingPreservesAgencyUniversally : Bool
ForgettingPreservesAgencyUniversally = false
