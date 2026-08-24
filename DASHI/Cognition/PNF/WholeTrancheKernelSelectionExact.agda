{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.WholeTrancheKernelSelectionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- WHOLE-TRANCHE KERNEL SELECTION
--
-- A kernel becomes an optimization target because measured tranche work shows
-- it dominates a declared workload, not because a local query looks expensive.
-- Replacement is then a separate theorem: authority must be exact and declared
-- work must improve on the same workload identity.
------------------------------------------------------------------------

record KernelWorkObservation
  (WorkloadId Kernel Work : Set)
  : Set₁ where
  field
    workloadId : WorkloadId
    kernel : Kernel
    observedWork : Work

open KernelWorkObservation public

record DominantKernel
  {WorkloadId Kernel Work : Set}
  (LeqWork : Work → Work → Set)
  (candidate : KernelWorkObservation WorkloadId Kernel Work)
  (other : KernelWorkObservation WorkloadId Kernel Work)
  : Set where
  field
    sameWorkload : workloadId candidate ≡ workloadId other
    otherWorkNoGreater : LeqWork (observedWork other) (observedWork candidate)

open DominantKernel public

record KernelReplacement
  (Input Authority Work : Set)
  (LeqWork : Work → Work → Set)
  : Set₁ where
  field
    oldKernel : Input → Authority
    newKernel : Input → Authority
    authorityExact : (input : Input) → newKernel input ≡ oldKernel input

    oldWork : Input → Work
    newWork : Input → Work
    workImproved : (input : Input) → LeqWork (newWork input) (oldWork input)

open KernelReplacement public

replacementPreservesAuthority :
  ∀ {Input Authority Work : Set}
    {LeqWork : Work → Work → Set}
    (replacement : KernelReplacement Input Authority Work LeqWork)
    (input : Input) →
  newKernel replacement input ≡ oldKernel replacement input
replacementPreservesAuthority replacement = authorityExact replacement

replacementCarriesDeclaredWorkImprovement :
  ∀ {Input Authority Work : Set}
    {LeqWork : Work → Work → Set}
    (replacement : KernelReplacement Input Authority Work LeqWork)
    (input : Input) →
  LeqWork (newWork replacement input) (oldWork replacement input)
replacementCarriesDeclaredWorkImprovement replacement = workImproved replacement

------------------------------------------------------------------------
-- Anti-confusion boundaries.
------------------------------------------------------------------------

data LocalSlownessProvesTrancheDominancePermission : Set where

data WallClockWinProvesAuthorityExactPermission : Set where

localSlownessDoesNotProveTrancheDominance :
  LocalSlownessProvesTrancheDominancePermission → ⊥
localSlownessDoesNotProveTrancheDominance ()

wallClockWinDoesNotProveAuthorityExact :
  WallClockWinProvesAuthorityExactPermission → ⊥
wallClockWinDoesNotProveAuthorityExact ()
