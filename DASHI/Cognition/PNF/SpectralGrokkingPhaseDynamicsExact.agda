module DASHI.Cognition.PNF.SpectralGrokkingPhaseDynamicsExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.GrokkingTaskCharacterPhaseExact as Character
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

------------------------------------------------------------------------
-- SPECTRAL GROKKING PROGRESS
--
-- The task-character law is already generic.  This module adds a finite
-- learning trajectory in which character-aligned structure rises before the
-- coarse held-out behaviour changes.  It is a theorem about this exact model,
-- not a claim that production gradient dynamics universally follow three steps.
------------------------------------------------------------------------

data LearningTime : Set where
  memorizing characterFormation cleanup : LearningTime

characterAmplitude : LearningTime → Nat
characterAmplitude memorizing = 0
characterAmplitude characterFormation = 1
characterAmplitude cleanup = 2

heldOutCorrect : LearningTime → Bool
heldOutCorrect memorizing = false
heldOutCorrect characterFormation = false
heldOutCorrect cleanup = true

trainingCorrect : LearningTime → Bool
trainingCorrect stage = true

characterAmplitudeRisesBeforeBehaviorMoves :
  characterAmplitude memorizing < characterAmplitude characterFormation
  × heldOutCorrect memorizing ≡ heldOutCorrect characterFormation
characterAmplitudeRisesBeforeBehaviorMoves = s≤s z≤n , refl

spectralStrengthContinuesThroughCleanup :
  characterAmplitude characterFormation < characterAmplitude cleanup
spectralStrengthContinuesThroughCleanup = s≤s (s≤s z≤n)

behaviorMovesOnlyAfterLatentCharacterPresent :
  characterAmplitude characterFormation ≡ 1
  × heldOutCorrect characterFormation ≡ false
  × heldOutCorrect cleanup ≡ true
behaviorMovesOnlyAfterLatentCharacterPresent = refl , refl , refl

trainingObservableFlatAcrossWholeTrajectory :
  trainingCorrect memorizing ≡ trainingCorrect characterFormation
  × trainingCorrect characterFormation ≡ trainingCorrect cleanup
trainingObservableFlatAcrossWholeTrajectory = refl , refl

------------------------------------------------------------------------
-- Concrete character computation remains tied to task symmetry.
------------------------------------------------------------------------

spectralPhaseForPair :
  Wheel.DepthWheelPhase →
  Wheel.DepthWheelPhase →
  Wheel.DepthWheelPhase
spectralPhaseForPair left right =
  Character.character Character.c3CharacterModel
    (Character.taskCompose Character.c3CharacterModel left right)

spectralPhaseIsCharacterComposition :
  (left right : Wheel.DepthWheelPhase) →
  spectralPhaseForPair left right
  ≡ Character.phaseCompose Character.c3CharacterModel
      (Character.character Character.c3CharacterModel left)
      (Character.character Character.c3CharacterModel right)
spectralPhaseIsCharacterComposition = Character.c3CharacterCompositionExact

heldOutTwoPlusTwoUsesWrappedCharacter :
  spectralPhaseForPair Wheel.phase-2 Wheel.phase-2 ≡ Wheel.phase-1
heldOutTwoPlusTwoUsesWrappedCharacter = refl

------------------------------------------------------------------------
-- Signed-zero analogy made precise as a *separate* learning-direction carrier:
-- equal coarse behavioural zero can contain different progression directions.
------------------------------------------------------------------------

data ZeroProgressDirection : Set where
  approachingGeneralization leavingPlateau : ZeroProgressDirection

record PreGeneralizationState : Set where
  constructor preGeneralizationState
  field
    visibleGain : Nat
    direction : ZeroProgressDirection

open PreGeneralizationState public

approachingState leavingState : PreGeneralizationState
approachingState = preGeneralizationState 0 approachingGeneralization
leavingState = preGeneralizationState 0 leavingPlateau

sameVisibleZeroGain : visibleGain approachingState ≡ visibleGain leavingState
sameVisibleZeroGain = refl

advanceGain : PreGeneralizationState → Nat
advanceGain (preGeneralizationState 0 approachingGeneralization) = 0
advanceGain (preGeneralizationState 0 leavingPlateau) = 1
advanceGain (preGeneralizationState (suc n) direction) = suc n

equalZeroGainDoesNotDetermineLearningFuture :
  advanceGain approachingState ≡ advanceGain leavingState → ⊥
equalZeroGainDoesNotDetermineLearningFuture ()

------------------------------------------------------------------------
-- The direction carrier is intentionally not identified with signed physical
-- zero; it instantiates the same future-refinement pattern in learning space.
------------------------------------------------------------------------
