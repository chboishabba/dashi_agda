module DASHI.Physics.Plasma.ToroidalZeroBounceSupportPatchHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transition
import DASHI.Physics.Plasma.ToroidalZeroBounceSparseSupportExact as Sparse
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- SUPPORT PATCH HYPERFABRIC
--
-- Disconnected admissible support families are retained as distinct patches.
-- Refinement/reopening is transition-gated: a consumer counterexample may add
-- support locally, but an inadmissible deletion is not a cheap model move.
------------------------------------------------------------------------

record SupportPatchState
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor support-patch-state
  field
    patch : Sparse.SupportPatch
    adequacy : Sparse.SparseSupportConsumerAdequacy population patch
    hardPhysicsAdmissibleReceipt : Set
    mdlEligibleReceipt : Set
    stateReference : String

open SupportPatchState public

record SupportPatchHyperformal
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor support-patch-hyperformal
  field
    State : Set
    decode : State → SupportPatchState population
    transitionSystem : Transition.AdmissibleTransitionSystem
    sameStateCarrierReceipt : Transition.State transitionSystem ≡ State
    supportDeletionMoveReceipt : Set
    supportReopenMoveReceipt : Set
    deletionRequiresConsumerPreservationReceipt : Set
    reopenRequiresCounterexampleReceipt : Set
    disconnectedPatchReceipt : Set
    hyperfabricReference : String

open SupportPatchHyperformal public

record SupportPatchBoundary : Set where
  constructor support-patch-boundary
  field
    allSupportSubsetsBelongToOneContinuousPatch : Bool
    allSupportSubsetsBelongToOneContinuousPatchIsFalse :
      allSupportSubsetsBelongToOneContinuousPatch ≡ false

    failedSparsePatchMayBeRepairedByLocalReopening : Bool
    failedSparsePatchMayBeRepairedByLocalReopeningIsTrue :
      failedSparsePatchMayBeRepairedByLocalReopening ≡ true

    supportDeletionIsAdmissibleBecauseItReducesMDL : Bool
    supportDeletionIsAdmissibleBecauseItReducesMDLIsFalse :
      supportDeletionIsAdmissibleBecauseItReducesMDL ≡ false

canonicalSupportPatchBoundary : SupportPatchBoundary
canonicalSupportPatchBoundary =
  support-patch-boundary
    false refl
    true refl
    false refl

patchReference : String
patchReference =
  "Admissible support subsets are hyperfabric patches; counterexamples reopen local support rather than permitting MDL to override consumer physics."
