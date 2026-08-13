module DASHI.Cognition.PNF.LearningProvenanceFutureExact where

open import DASHI.Core.Prelude

import DASHI.Core.PathDependentAccessibilityExact as Path

------------------------------------------------------------------------
-- LEARNING-PROVENANCE FUTURES
--
-- Equal current parameters/output do not determine equal future learning when
-- optimizer/curriculum provenance remains part of the true learning state.
------------------------------------------------------------------------

data Parameter : Set where
  neutral specialized : Parameter

data OptimizerProvenance : Set where
  warmMomentum coldMomentum : OptimizerProvenance

data LearningAction : Set where
  trainOnce : LearningAction

record Learner : Set where
  constructor learner
  field
    parameter : Parameter
    optimizerProvenance : OptimizerProvenance

open Learner public

currentOutput : Learner → Bool
currentOutput (learner neutral provenance) = false
currentOutput (learner specialized provenance) = true

learningUpdate : OptimizerProvenance → LearningAction → Learner → Learner
learningUpdate warmMomentum trainOnce (learner neutral provenance) =
  learner specialized warmMomentum
learningUpdate coldMomentum trainOnce (learner neutral provenance) =
  learner neutral coldMomentum
learningUpdate provenance trainOnce (learner specialized old) =
  learner specialized provenance

sameParametersDifferentProvenanceLeft sameParametersDifferentProvenanceRight : Learner
sameParametersDifferentProvenanceLeft = learner neutral warmMomentum
sameParametersDifferentProvenanceRight = learner neutral coldMomentum

sameCurrentParameters :
  parameter sameParametersDifferentProvenanceLeft
  ≡ parameter sameParametersDifferentProvenanceRight
sameCurrentParameters = refl

sameCurrentOutputs :
  currentOutput sameParametersDifferentProvenanceLeft
  ≡ currentOutput sameParametersDifferentProvenanceRight
sameCurrentOutputs = refl

sameTrainingActionProducesDifferentFutureOutput :
  currentOutput
    (learningUpdate
      (optimizerProvenance sameParametersDifferentProvenanceLeft)
      trainOnce sameParametersDifferentProvenanceLeft)
  ≡
  currentOutput
    (learningUpdate
      (optimizerProvenance sameParametersDifferentProvenanceRight)
      trainOnce sameParametersDifferentProvenanceRight)
  → ⊥
sameTrainingActionProducesDifferentFutureOutput ()

------------------------------------------------------------------------
-- Reuse the repository's path-dependent accessibility abstraction exactly:
-- optimizer provenance selects the learning transition geometry.
------------------------------------------------------------------------

learningAsPathDependentAccessibility :
  Path.PathDependentAccessibility Learner OptimizerProvenance LearningAction
learningAsPathDependentAccessibility =
  Path.pathDependentAccessibility
    currentOutput
    optimizerProvenance
    learningUpdate

sameParameterStateHasDifferentLearningFuture :
  Path.AccessibilityDivergence learningAsPathDependentAccessibility
sameParameterStateHasDifferentLearningFuture =
  Path.accessibilityDivergence
    trainOnce
    sameParametersDifferentProvenanceLeft
    sameParametersDifferentProvenanceRight
    refl
    sameTrainingActionProducesDifferentFutureOutput

------------------------------------------------------------------------
-- Consequence: parameter equality is not a complete learning-state quotient.
-- Optimizer/curriculum/replay provenance can be causally relevant even when
-- inference output and parameter projection currently agree.
------------------------------------------------------------------------
