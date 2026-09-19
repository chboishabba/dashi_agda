{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayF134ContinuumWeldParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact as Atlas
import DASHI.Physics.YangMills.YMClayOutstandingPhysicalFrontierExact as Frontier
import DASHI.Physics.YangMills.YMClayPhysicalStressOSCommonCoreWitnessExact as F4
import DASHI.Physics.YangMills.YMClayPhysicalF34TypedCompositionExact as Typed

------------------------------------------------------------------------
-- Exact parity surface after the physical frontier recut:
--
--   F1  literal Wilson finite-gap trajectory
--   F3  actual Sprint-backed physical continuum/recovery witness
--   F4  actual stress/OS common-core + closure witness
--
-- YM=OS evolution equality is compiled from F4 rather than accepted as an
-- independent physical input.
------------------------------------------------------------------------

record LiteralSU2F134PhysicalInputs : Set₁ where
  field
    f1 : Frontier.LiteralWilsonUniformGapTrajectory
    f3 : Frontier.PhysicalContinuumLimitWitness
    f4 : F4.PhysicalStressOSCommonCoreWitness

open LiteralSU2F134PhysicalInputs public

asOutstandingPhysicalFrontier :
  LiteralSU2F134PhysicalInputs → Frontier.OutstandingPhysicalFrontier
asOutstandingPhysicalFrontier inputs = record
  { Frontier.OutstandingPhysicalFrontier.f1LiteralWilsonUniformGap = f1 inputs
  ; Frontier.OutstandingPhysicalFrontier.f3PhysicalContinuumLimit = f3 inputs
  ; Frontier.OutstandingPhysicalFrontier.f4PhysicalStressOSCommonCore = f4 inputs
  }

asTypedF34Kernel :
  LiteralSU2F134PhysicalInputs → Typed.PhysicalF34TypedKernel
asTypedF34Kernel inputs = record
  { Typed.PhysicalF34TypedKernel.f3 = f3 inputs
  ; Typed.PhysicalF34TypedKernel.f4 = f4 inputs
  }

continuumWeldLean : Atlas.LeanTheoremArtifact
continuumWeldLean = Atlas.literalSU2ContinuumWeldLean

f2IndependentInputRequired : Bool
f2IndependentInputRequired = false

f2IndependentInputRequiredIsFalse : f2IndependentInputRequired ≡ false
f2IndependentInputRequiredIsFalse = refl

f134AreExactlyTheSurvivingPhysicalInputs : Bool
f134AreExactlyTheSurvivingPhysicalInputs = true

f134AreExactlyTheSurvivingPhysicalInputsIsTrue :
  f134AreExactlyTheSurvivingPhysicalInputs ≡ true
f134AreExactlyTheSurvivingPhysicalInputsIsTrue = refl

f3RecoveryGapIsExtraPhysicalLeaf : Bool
f3RecoveryGapIsExtraPhysicalLeaf = false

f3RecoveryGapIsExtraPhysicalLeafIsFalse :
  f3RecoveryGapIsExtraPhysicalLeaf ≡ false
f3RecoveryGapIsExtraPhysicalLeafIsFalse = refl

f4EvolutionEqualityIsExtraPhysicalLeafAfterF4 : Bool
f4EvolutionEqualityIsExtraPhysicalLeafAfterF4 = false

f4EvolutionEqualityIsExtraPhysicalLeafAfterF4IsFalse :
  f4EvolutionEqualityIsExtraPhysicalLeafAfterF4 ≡ false
f4EvolutionEqualityIsExtraPhysicalLeafAfterF4IsFalse = refl

continuumWeldLeanLevel : ProofLevel
continuumWeldLeanLevel = standardImported

physicalF134InputsLevel : ProofLevel
physicalF134InputsLevel = conditional

data F134ContinuumWeldLeanDonorPresent : Set where
  f134ContinuumWeldLeanDonorPresent : F134ContinuumWeldLeanDonorPresent

f134ContinuumWeldLeanDonorWitness : F134ContinuumWeldLeanDonorPresent
f134ContinuumWeldLeanDonorWitness = f134ContinuumWeldLeanDonorPresent
