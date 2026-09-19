{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2D2R129CompositeConvergenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified
import DASHI.Physics.YangMills.BalabanUnifiedCompletedStateProjectionExact as Completed

------------------------------------------------------------------------
-- D2d / CORRECT SAME-FAMILY ENDPOINT: CONVERGENCE, NOT FINITE-DEPTH EQUALITY
--
-- The unified RG lane already has the mathematically natural object:
--
--   scale |-> compositeProjection(stateAtScale scale)
--
-- and the completed-state owner proves that this sequence converges to
--
--   compositeProjection(limitState).
--
-- Therefore D2d must not require a selected finite RG depth to equal the
-- continuum completed composite exactly.  The physical same-family theorem is
-- convergence of the actual scale-indexed operator/composite trajectory to the
-- completed R129 projection, followed by identification of that completed
-- projection with R129's completed composite.
------------------------------------------------------------------------

unifiedCompositeTrajectory :
  ∀ {State Ordinary Composite Correlation Bound}
    (dataSet : Completed.UnifiedCompletedStateAuthority
      State Ordinary Composite Correlation Bound) →
  Nat → Composite
unifiedCompositeTrajectory dataSet scale =
  Unified.compositeProjection
    (Completed.normAuthority dataSet)
    (Completed.stateAtScale dataSet scale)

unifiedCompletedComposite :
  ∀ {State Ordinary Composite Correlation Bound}
    (dataSet : Completed.UnifiedCompletedStateAuthority
      State Ordinary Composite Correlation Bound) →
  Composite
unifiedCompletedComposite dataSet =
  Unified.compositeProjection
    (Completed.normAuthority dataSet)
    (Completed.limitState dataSet)

unifiedCompositeTrajectoryConverges :
  ∀ {State Ordinary Composite Correlation Bound}
    (dataSet : Completed.UnifiedCompletedStateAuthority
      State Ordinary Composite Correlation Bound) →
  Completed.CompositeConverges dataSet
    (unifiedCompositeTrajectory dataSet)
    (unifiedCompletedComposite dataSet)
unifiedCompositeTrajectoryConverges dataSet =
  Completed.compositeProjectionContinuous dataSet
    (Completed.unifiedStateConverges dataSet)

finiteDepthEqualsCompletedCompositeRequired : Bool
finiteDepthEqualsCompletedCompositeRequired = false

finiteDepthEqualsCompletedCompositeRequiredIsFalse :
  finiteDepthEqualsCompletedCompositeRequired ≡ false
finiteDepthEqualsCompletedCompositeRequiredIsFalse = refl

sameFamilyCompositeConvergenceRequired : Bool
sameFamilyCompositeConvergenceRequired = true

sameFamilyCompositeConvergenceRequiredIsTrue :
  sameFamilyCompositeConvergenceRequired ≡ true
sameFamilyCompositeConvergenceRequiredIsTrue = refl

unifiedCompositeCompletionCompilerLevel : ProofLevel
unifiedCompositeCompletionCompilerLevel =
  Completed.unifiedCompletedStateProjectionLevel

physicalUnifiedCompletionExistenceLevel : ProofLevel
physicalUnifiedCompletionExistenceLevel =
  Completed.physicalUnifiedCompletedStateExistenceLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
