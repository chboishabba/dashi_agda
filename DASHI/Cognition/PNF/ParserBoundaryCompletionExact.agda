module DASHI.Cognition.PNF.ParserBoundaryCompletionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Boundary completion under exactly-once authority.
--
-- The structural owner of a sentence is fixed by its canonical source anchor.
-- Physical context/repair observations may supply missing parser evidence, but
-- they never become a second semantic owner. Publication is permitted only
-- once the owner's sentence observation is complete.
------------------------------------------------------------------------

record BoundaryCompletionKernel : Set₁ where
  constructor boundaryCompletionKernel
  field
    SourceAnchor : Set
    StructuralOwner : Set
    Observation : Set
    CompletedObservation : Set

    owner : SourceAnchor → StructuralOwner
    anchor : Observation → SourceAnchor
    completedAnchor : CompletedObservation → SourceAnchor

    IsComplete : Observation → Set
    complete : (observation : Observation) → IsComplete observation → CompletedObservation

    -- Completion preserves the original source anchor. Evidence suppliers may
    -- differ physically from the owner but cannot change semantic ownership.
    completionPreservesAnchor :
      (observation : Observation) (receipt : IsComplete observation) →
      completedAnchor (complete observation receipt) ≡ anchor observation

open BoundaryCompletionKernel public

record OwnerCompletionReceipt (kernel : BoundaryCompletionKernel) : Set₁ where
  constructor ownerCompletionReceipt
  field
    sourceAnchor : SourceAnchor kernel
    authorityOwner : StructuralOwner kernel
    completedObservation : CompletedObservation kernel

    ownerExact : authorityOwner ≡ owner kernel sourceAnchor
    completedAnchorExact :
      completedAnchor kernel completedObservation ≡ sourceAnchor

open OwnerCompletionReceipt public

------------------------------------------------------------------------
-- Invalid architectures.
------------------------------------------------------------------------

data IncompleteOwnerObservationMayPublish : Set where

data RepairEvidenceBecomesSecondOwner : Set where

data CompletionMayChangeSourceAnchor : Set where

incompleteObservationCannotPublish : IncompleteOwnerObservationMayPublish → ⊥
incompleteObservationCannotPublish ()

repairEvidenceDoesNotBecomeOwner : RepairEvidenceBecomesSecondOwner → ⊥
repairEvidenceDoesNotBecomeOwner ()

completionCannotMoveAnchor : CompletionMayChangeSourceAnchor → ⊥
completionCannotMoveAnchor ()
