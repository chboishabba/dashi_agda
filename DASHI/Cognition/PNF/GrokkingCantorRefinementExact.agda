module DASHI.Cognition.PNF.GrokkingCantorRefinementExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.CantorCylinderMassExact as Cantor

------------------------------------------------------------------------
-- GROKKING / CANTOR REFINEMENT, NOT IDENTIFICATION
------------------------------------------------------------------------

data LearningStage : Set where
  memorizationStage circuitFormationStage cleanupStage : LearningStage

trainingMassNumerator : LearningStage → Nat
trainingMassNumerator memorizationStage = 1
trainingMassNumerator circuitFormationStage = 1
trainingMassNumerator cleanupStage = 1

taskMassNumerator : LearningStage → Nat
taskMassNumerator memorizationStage = 0
taskMassNumerator circuitFormationStage = 0
taskMassNumerator cleanupStage = 1

mechanismMassNumerator : LearningStage → Nat
mechanismMassNumerator memorizationStage = 0
mechanismMassNumerator circuitFormationStage = 1
mechanismMassNumerator cleanupStage = 1

supportComplexity : LearningStage → Nat
supportComplexity memorizationStage = 3
supportComplexity circuitFormationStage = 2
supportComplexity cleanupStage = 1

trainingMassRemainsUnitThroughout :
  (stage : LearningStage) → trainingMassNumerator stage ≡ 1
trainingMassRemainsUnitThroughout memorizationStage = refl
trainingMassRemainsUnitThroughout circuitFormationStage = refl
trainingMassRemainsUnitThroughout cleanupStage = refl

latentMechanismPrecedesVisibleTaskCoverage :
  mechanismMassNumerator circuitFormationStage ≡ 1
  × taskMassNumerator circuitFormationStage ≡ 0
latentMechanismPrecedesVisibleTaskCoverage = refl , refl

supportComplexityDropsDuringCircuitFormation :
  supportComplexity circuitFormationStage < supportComplexity memorizationStage
supportComplexityDropsDuringCircuitFormation = s≤s (s≤s (s≤s z≤n))

supportComplexityDropsDuringCleanup :
  supportComplexity cleanupStage < supportComplexity circuitFormationStage
supportComplexityDropsDuringCleanup = s≤s (s≤s z≤n)

taskCoverageRisesAtCleanup :
  taskMassNumerator circuitFormationStage < taskMassNumerator cleanupStage
taskCoverageRisesAtCleanup = s≤s z≤n

compressionAndGeneralizationCanMoveTogether :
  supportComplexity cleanupStage < supportComplexity circuitFormationStage
  × taskMassNumerator circuitFormationStage < taskMassNumerator cleanupStage
compressionAndGeneralizationCanMoveTogether =
  supportComplexityDropsDuringCleanup , taskCoverageRisesAtCleanup

------------------------------------------------------------------------
-- Cantor accounting stays a separate certificate.
------------------------------------------------------------------------

record CantorIndexedLearningStage : Set where
  constructor cantorIndexedLearningStage
  field
    cantorDepth : Nat
    learningStage : LearningStage

open CantorIndexedLearningStage public

cantorLayerRemainsUnitAtEveryLearningStage :
  (indexed : CantorIndexedLearningStage) →
  Cantor.totalNumerator (Cantor.polarLayerHasUnitMass (cantorDepth indexed))
  ≡ Cantor.commonDenominator (Cantor.polarLayerHasUnitMass (cantorDepth indexed))
cantorLayerRemainsUnitAtEveryLearningStage indexed =
  Cantor.normalizedUnitExact (Cantor.polarLayerHasUnitMass (cantorDepth indexed))

------------------------------------------------------------------------
-- Thus 1_training, 1_Cantor, 1_mechanism, and 1_task remain indexed notions.
------------------------------------------------------------------------
