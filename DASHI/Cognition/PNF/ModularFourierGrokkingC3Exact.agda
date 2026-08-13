module DASHI.Cognition.PNF.ModularFourierGrokkingC3Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.GrokkingTaskCharacterPhaseExact as Character
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

------------------------------------------------------------------------
-- SOURCES
--
-- Alethea Power, Yuri Burda, Harri Edwards, Igor Babuschkin, Vedant Misra,
-- "Grokking: Generalization Beyond Overfitting on Small Algorithmic Datasets",
-- arXiv:2201.02177.  No DOI asserted here.
--
-- Neel Nanda, Lawrence Chan, Tom Lieberum, Jess Smith, Jacob Steinhardt,
-- "Progress measures for grokking via mechanistic interpretability",
-- arXiv:2301.05217.  No DOI asserted here.
--
-- Andrey Gromov, "Grokking modular arithmetic", arXiv:2301.02679.
-- No DOI asserted here.
--
-- This is an exact finite C3 modular task, not a mechanistic claim about the
-- networks studied in those papers.
------------------------------------------------------------------------

powerTitle : String
powerTitle = "Grokking: Generalization Beyond Overfitting on Small Algorithmic Datasets"

nandaTitle : String
nandaTitle = "Progress measures for grokking via mechanistic interpretability"

gromovTitle : String
gromovTitle = "Grokking modular arithmetic"

data InputPair : Set where
  p00 p01 p02 p10 p11 p12 p20 p21 p22 : InputPair

leftPhase : InputPair → Wheel.DepthWheelPhase
leftPhase p00 = Wheel.phase-0
leftPhase p01 = Wheel.phase-0
leftPhase p02 = Wheel.phase-0
leftPhase p10 = Wheel.phase-1
leftPhase p11 = Wheel.phase-1
leftPhase p12 = Wheel.phase-1
leftPhase p20 = Wheel.phase-2
leftPhase p21 = Wheel.phase-2
leftPhase p22 = Wheel.phase-2

rightPhase : InputPair → Wheel.DepthWheelPhase
rightPhase p00 = Wheel.phase-0
rightPhase p01 = Wheel.phase-1
rightPhase p02 = Wheel.phase-2
rightPhase p10 = Wheel.phase-0
rightPhase p11 = Wheel.phase-1
rightPhase p12 = Wheel.phase-2
rightPhase p20 = Wheel.phase-0
rightPhase p21 = Wheel.phase-1
rightPhase p22 = Wheel.phase-2

algorithmicRule : InputPair → Wheel.DepthWheelPhase
algorithmicRule pair =
  Character.taskCompose Character.c3CharacterModel
    (leftPhase pair) (rightPhase pair)

-- A memorizer agrees with the algorithm on all eight observed examples but has
-- no correct structural rule for the held-out p22 point.
memorizerRule : InputPair → Wheel.DepthWheelPhase
memorizerRule p00 = Wheel.phase-0
memorizerRule p01 = Wheel.phase-1
memorizerRule p02 = Wheel.phase-2
memorizerRule p10 = Wheel.phase-1
memorizerRule p11 = Wheel.phase-2
memorizerRule p12 = Wheel.phase-0
memorizerRule p20 = Wheel.phase-2
memorizerRule p21 = Wheel.phase-0
memorizerRule p22 = Wheel.phase-0

data TrainingPair : InputPair → Set where
  train00 : TrainingPair p00
  train01 : TrainingPair p01
  train02 : TrainingPair p02
  train10 : TrainingPair p10
  train11 : TrainingPair p11
  train12 : TrainingPair p12
  train20 : TrainingPair p20
  train21 : TrainingPair p21

memorizerFitsEveryTrainingPair :
  (pair : InputPair) → TrainingPair pair →
  memorizerRule pair ≡ algorithmicRule pair
memorizerFitsEveryTrainingPair p00 train00 = refl
memorizerFitsEveryTrainingPair p01 train01 = refl
memorizerFitsEveryTrainingPair p02 train02 = refl
memorizerFitsEveryTrainingPair p10 train10 = refl
memorizerFitsEveryTrainingPair p11 train11 = refl
memorizerFitsEveryTrainingPair p12 train12 = refl
memorizerFitsEveryTrainingPair p20 train20 = refl
memorizerFitsEveryTrainingPair p21 train21 = refl
memorizerFitsEveryTrainingPair p22 ()

heldOutCorrectAnswer : algorithmicRule p22 ≡ Wheel.phase-1
heldOutCorrectAnswer = refl

heldOutMemorizerAnswer : memorizerRule p22 ≡ Wheel.phase-0
heldOutMemorizerAnswer = refl

heldOutPointSeparatesMemorizationFromAlgorithm :
  memorizerRule p22 ≡ algorithmicRule p22 → ⊥
heldOutPointSeparatesMemorizationFromAlgorithm ()

record TrainingEquivalent
    (left right : InputPair → Wheel.DepthWheelPhase) : Set₁ where
  constructor trainingEquivalent
  field
    agreesOnTraining :
      (pair : InputPair) → TrainingPair pair → left pair ≡ right pair

open TrainingEquivalent public

record FullTaskEquivalent
    (left right : InputPair → Wheel.DepthWheelPhase) : Set₁ where
  constructor fullTaskEquivalent
  field
    agreesEverywhere : (pair : InputPair) → left pair ≡ right pair

open FullTaskEquivalent public

memorizerAndAlgorithmTrainingEquivalent :
  TrainingEquivalent memorizerRule algorithmicRule
memorizerAndAlgorithmTrainingEquivalent =
  trainingEquivalent memorizerFitsEveryTrainingPair

memorizerAndAlgorithmNotFullTaskEquivalent :
  FullTaskEquivalent memorizerRule algorithmicRule → ⊥
memorizerAndAlgorithmNotFullTaskEquivalent equivalent =
  heldOutPointSeparatesMemorizationFromAlgorithm
    (agreesEverywhere equivalent p22)

-- The generalizing rule is not merely a lookup table: it is the supplied C3
-- task-character composition law from the phase abstraction.
algorithmicRuleIsCharacterComposition :
  (pair : InputPair) →
  algorithmicRule pair
  ≡ Character.phaseComposeC3 (leftPhase pair) (rightPhase pair)
algorithmicRuleIsCharacterComposition pair = refl

------------------------------------------------------------------------
-- Exact grokking lesson: unit fit on the declared training support does not
-- determine the extension to the full task.  A phase/character law supplies a
-- structural extension that the memorizer lacks.
------------------------------------------------------------------------
