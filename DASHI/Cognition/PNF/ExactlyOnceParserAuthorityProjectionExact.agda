module DASHI.Cognition.PNF.ExactlyOnceParserAuthorityProjectionExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Exactly-once authority projection for overlapping parser observations.
--
-- Parser partitions, bilateral context windows, repairs, retries, and future
-- finer streaming schedules may observe the same canonical source material.
-- Observation is not authority.  Every authority-bearing source event has one
-- canonical structural owner selected by its source anchor; all other physical
-- observations are evidence-only.
------------------------------------------------------------------------

record ExactlyOnceAuthorityProjection : Set₁ where
  constructor exactlyOnceAuthorityProjection
  field
    Observation : Set
    OwnedEvent : Set
    SourceAnchor : Set
    StructuralOwner : Set

    anchor : Observation → SourceAnchor
    owner : SourceAnchor → StructuralOwner

    -- The projection is the only authority-bearing exit from parser
    -- observations into the semantic fold.
    projectOwned : Observation → OwnedEvent
    ownedAnchor : OwnedEvent → SourceAnchor

    -- Physical observations of the same source anchor project to the same
    -- authority-bearing identity.  Context, repair, retry, and scheduling
    -- identity therefore cannot mint another semantic event.
    SameAnchor : Observation → Observation → Set
    sameAnchorProjectsSameAuthority :
      (x y : Observation) → SameAnchor x y →
      ownedAnchor (projectOwned x) ≡ ownedAnchor (projectOwned y)

    -- Ownership is total and single-valued at the canonical source anchor.
    ExactOwner : SourceAnchor → StructuralOwner → Set
    ownerExists : (a : SourceAnchor) → ExactOwner a (owner a)
    ownerUnique :
      (a : SourceAnchor) (candidate : StructuralOwner) →
      ExactOwner a candidate → candidate ≡ owner a

open ExactlyOnceAuthorityProjection public

------------------------------------------------------------------------
-- Physical roles are deliberately separated from semantic authority.
------------------------------------------------------------------------

data PhysicalObservationRole : Set where
  structuralOwner : PhysicalObservationRole
  structuralContext : PhysicalObservationRole
  boundaryRepair : PhysicalObservationRole
  retryObservation : PhysicalObservationRole

record ObservationAdmission : Set where
  constructor observationAdmission
  field
    role : PhysicalObservationRole
    authorityBearing : Set

open ObservationAdmission public

-- Only the canonical structural owner may be an authority-bearing parser
-- producer.  Repair/context/retry observations may refine evidence or resolve
-- obligations but never directly mint another owned semantic event.
data ContextObservationMintsAuthority : Set where
data RepairObservationMintsAuthority : Set where
data RetryObservationMintsAuthority : Set where

data PhysicalPartitionIdentityIsSemanticIdentity : Set where

contextCannotMintAuthority : ContextObservationMintsAuthority → ⊥
contextCannotMintAuthority ()

repairCannotMintAuthority : RepairObservationMintsAuthority → ⊥
repairCannotMintAuthority ()

retryCannotMintAuthority : RetryObservationMintsAuthority → ⊥
retryCannotMintAuthority ()

partitionIdentityIsNotSemanticIdentity : PhysicalPartitionIdentityIsSemanticIdentity → ⊥
partitionIdentityIsNotSemanticIdentity ()

------------------------------------------------------------------------
-- Schedule-invariance receipt.
--
-- Coarse and refined physical schedules may differ arbitrarily in partition
-- count/context/repairs.  Performance comparison is admissible only after both
-- schedules project to the same owned stream and final consumer authority.
------------------------------------------------------------------------

record ScheduleAuthorityParityReceipt : Set₁ where
  constructor scheduleAuthorityParityReceipt
  field
    CoarseOwnedStream : Set
    RefinedOwnedStream : Set
    FinalAuthority : Set

    SameOwnedStream : Set
    sameOwnedStream : SameOwnedStream

    SameFinalAuthority : Set
    sameFinalAuthority : SameFinalAuthority

open ScheduleAuthorityParityReceipt public

data TimingWithoutAuthorityParityIsOptimizationEvidence : Set where

timingWithoutParityIsNotEvidence : TimingWithoutAuthorityParityIsOptimizationEvidence → ⊥
timingWithoutParityIsNotEvidence ()
