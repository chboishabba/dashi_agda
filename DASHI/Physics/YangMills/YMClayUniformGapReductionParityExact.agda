{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayUniformGapReductionParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact as Atlas

------------------------------------------------------------------------
-- Aristotle 2026-09-17 literal Wilson uniform-gap reduction parity.
--
-- Donor theorem family:
--   RequestProject/YangMills/Lattice/UniformGapReduction.lean
--
-- On the literal Wilson physical vacuum complement the finite transfer-form
-- problem is reduced to one decorrelation estimate
--
--   |<P0 psi, P1 psi>| <= c ||psi||^2,
--
-- which yields the finite form gap a^-1 (1-c).  A c uniform on the chosen
-- physical trajectory together with Delta <= a_k^-1 (1-c) is exactly the
-- uniform-gap input consumed by the varying-carrier continuum weld.
--
-- The donor also checks c = 0 at zero coupling uniformly in volume.  That is a
-- diagnostic/non-vacuity result, not the interacting beta(a)->infinity
-- continuum-trajectory estimate.
------------------------------------------------------------------------

uniformGapReductionLean : Atlas.LeanTheoremArtifact
uniformGapReductionLean = Atlas.literalSU2UniformGapReductionLean

zeroCouplingUniformGapLean : Atlas.LeanTheoremArtifact
zeroCouplingUniformGapLean = Atlas.literalSU2ZeroCouplingUniformGapLean

literalWilsonGapReducedToDecorrelator : Bool
literalWilsonGapReducedToDecorrelator = true

literalWilsonGapReducedToDecorrelatorIsTrue :
  literalWilsonGapReducedToDecorrelator ≡ true
literalWilsonGapReducedToDecorrelatorIsTrue = refl

zeroCouplingGapUniformInVolume : Bool
zeroCouplingGapUniformInVolume = true

zeroCouplingGapUniformInVolumeIsTrue :
  zeroCouplingGapUniformInVolume ≡ true
zeroCouplingGapUniformInVolumeIsTrue = refl

interactingContinuumTrajectoryUniformGapProvedByDonor : Bool
interactingContinuumTrajectoryUniformGapProvedByDonor = false

interactingContinuumTrajectoryUniformGapProvedByDonorIsFalse :
  interactingContinuumTrajectoryUniformGapProvedByDonor ≡ false
interactingContinuumTrajectoryUniformGapProvedByDonorIsFalse = refl

uniformGapReductionLeanLevel : ProofLevel
uniformGapReductionLeanLevel = standardImported

interactingContinuumTrajectoryGapLevel : ProofLevel
interactingContinuumTrajectoryGapLevel = conditional

data UniformGapReductionLeanDonorPresent : Set where
  uniformGapReductionLeanDonorPresent : UniformGapReductionLeanDonorPresent

uniformGapReductionLeanDonorWitness : UniformGapReductionLeanDonorPresent
uniformGapReductionLeanDonorWitness = uniformGapReductionLeanDonorPresent
