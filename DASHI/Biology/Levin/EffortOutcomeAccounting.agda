module DASHI.Biology.Levin.EffortOutcomeAccounting where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Explicitly account for the conventional sources of task-specific
-- competence before introducing any stronger latent-pattern explanation.

record ConventionalEffort : Set where
  field
    engineeredCost : Nat
    selectionCost  : Nat
    trainingCost   : Nat

record OutcomeComplexity : Set where
  field
    measuredCompetence : Nat
    taskSpecificity    : Nat
    robustness         : Nat

record EffortOutcomeResidual : Set where
  field
    effort      : ConventionalEffort
    outcome     : OutcomeComplexity
    accounted   : Nat
    unexplained : Nat
    accountingCloses :
      accounted + unexplained ≡ OutcomeComplexity.measuredCompetence outcome

record ResidualExplanationBoundary : Set where
  field
    inheritedPlasticityTested     : Bool
    genericDynamicalBiasTested    : Bool
    embodimentAffordanceTested    : Bool
    measurementArtifactTested     : Bool
    historicalSelectionTested     : Bool
    latentPatternHypothesisNeeded : Bool
    interpretation                : String

canonicalResidualExplanationBoundary : ResidualExplanationBoundary
canonicalResidualExplanationBoundary = record
  { inheritedPlasticityTested = false
  ; genericDynamicalBiasTested = false
  ; embodimentAffordanceTested = false
  ; measurementArtifactTested = false
  ; historicalSelectionTested = false
  ; latentPatternHypothesisNeeded = false
  ; interpretation = "An effort-outcome residual is a research target, not evidence by itself for a non-physical source"
  }

EffortGapImpliesPlatonicSourceByDefinition : Bool
EffortGapImpliesPlatonicSourceByDefinition = false

NovelCompetenceImpliesNoSelectionHistory : Bool
NovelCompetenceImpliesNoSelectionHistory = false

UnexplainedMeansUnexplainable : Bool
UnexplainedMeansUnexplainable = false
