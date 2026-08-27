module DASHI.Biology.IntrospectiveEmbodiedHyperformalismObservationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- INTROSPECTIVE VISUALIZATION -> CV -> FORMAL RECEIPT
--
-- This module formalizes only invariants recovered from a deterministic
-- visualization by an OpenCV observation pass.  The detector did not consume
-- the theory JSON or intended node counts.  Pixel topology is evidence about
-- the rendered representation, not theorem authority for neurobiology.
------------------------------------------------------------------------

data RecoveredSupervoxel : Set where
  recoveredS0 recoveredS1 recoveredS2 recoveredS3 : RecoveredSupervoxel

observedFibreCount : RecoveredSupervoxel → Nat
observedFibreCount recoveredS0 = 3
observedFibreCount recoveredS1 = 1
observedFibreCount recoveredS2 = 2
observedFibreCount recoveredS3 = 3

observedSupervoxelCount : Nat
observedSupervoxelCount = 4

observedTotalFibreCount : Nat
observedTotalFibreCount = 9

opencvRecoveredFourSupervoxels : observedSupervoxelCount ≡ 4
opencvRecoveredFourSupervoxels = refl

opencvRecoveredNineFibres : observedTotalFibreCount ≡ 9
opencvRecoveredNineFibres = refl

opencvRecoveredOccupancyProfile :
  observedFibreCount recoveredS0 ≡ 3
  × observedFibreCount recoveredS1 ≡ 1
  × observedFibreCount recoveredS2 ≡ 2
  × observedFibreCount recoveredS3 ≡ 3
opencvRecoveredOccupancyProfile = refl , (refl , (refl , refl))

broadAndContractedOccupancyDiffer :
  observedFibreCount recoveredS0 ≡ observedFibreCount recoveredS1 → ⊥
broadAndContractedOccupancyDiffer ()

contractedAndReopenedOccupancyDiffer :
  observedFibreCount recoveredS1 ≡ observedFibreCount recoveredS2 → ⊥
contractedAndReopenedOccupancyDiffer ()

broadAndGoalCompatibleShareRecoveredOccupancy :
  observedFibreCount recoveredS0 ≡ observedFibreCount recoveredS3
broadAndGoalCompatibleShareRecoveredOccupancy = refl

record IntrospectiveObservationBoundary : Set where
  constructor introspectiveObservationBoundary
  field
    cvRecoveredRenderedTopology : Bool
    cvRecoveredRenderedTopologyIsTrue : cvRecoveredRenderedTopology ≡ true
    pixelTopologyDeterminesBiologicalMechanism : Bool
    pixelTopologyDeterminesBiologicalMechanismIsFalse :
      pixelTopologyDeterminesBiologicalMechanism ≡ false
    recoveredOccupancyDeterminesClinicalMeaning : Bool
    recoveredOccupancyDeterminesClinicalMeaningIsFalse :
      recoveredOccupancyDeterminesClinicalMeaning ≡ false
    visualizationMayGenerateNewFormalObligations : Bool
    visualizationMayGenerateNewFormalObligationsIsTrue :
      visualizationMayGenerateNewFormalObligations ≡ true

canonicalIntrospectiveObservationBoundary : IntrospectiveObservationBoundary
canonicalIntrospectiveObservationBoundary =
  introspectiveObservationBoundary true refl false refl false refl true refl
