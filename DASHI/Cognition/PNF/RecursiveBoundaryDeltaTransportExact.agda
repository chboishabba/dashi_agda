module DASHI.Cognition.PNF.RecursiveBoundaryDeltaTransportExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- B2 generic hierarchy specialization.
--
-- Every hierarchy level owns a delta carrier.  Transport to the next parent
-- level preserves the fusion algebra exactly.  This is stronger than merely
-- requiring parent fusion to be associative: it states that batching before
-- transport and batching after transport are observationally identical.
------------------------------------------------------------------------

record RecursiveBoundaryDeltaArchitecture : Set₁ where
  field
    LevelDelta : Nat → Set

    emptyDelta :
      (level : Nat) →
      LevelDelta level

    fuseDelta :
      (level : Nat) →
      LevelDelta level →
      LevelDelta level →
      LevelDelta level

    transportToParent :
      (level : Nat) →
      LevelDelta level →
      LevelDelta (suc level)

    fuseAssociative :
      (level : Nat) →
      (left middle right : LevelDelta level) →
      fuseDelta level (fuseDelta level left middle) right
        ≡
      fuseDelta level left (fuseDelta level middle right)

    transportEmpty :
      (level : Nat) →
      transportToParent level (emptyDelta level)
        ≡
      emptyDelta (suc level)

    transportFusion :
      (level : Nat) →
      (left right : LevelDelta level) →
      transportToParent level (fuseDelta level left right)
        ≡
      fuseDelta (suc level)
        (transportToParent level left)
        (transportToParent level right)

open RecursiveBoundaryDeltaArchitecture public

------------------------------------------------------------------------
-- Physical work receipt.
--
-- The recursive path is charged to transported deltas and hierarchy hops.
-- There is deliberately no lower-carrier reconstruction term.  The concrete
-- runtime may additionally measure database batches and parent-local
-- reconciliation, but those are independent of this transport law.
------------------------------------------------------------------------

record RecursiveBoundaryDeltaWorkReceipt : Set where
  constructor recursiveBoundaryDeltaWorkReceipt
  field
    transportedDeltaCount : Nat
    hierarchyHopCount : Nat
    fusionInputCount : Nat
    sourceInteriorRescanCount : Nat
    noSourceInteriorRescan : sourceInteriorRescanCount ≡ zero

open RecursiveBoundaryDeltaWorkReceipt public

------------------------------------------------------------------------
-- Negative boundaries.
------------------------------------------------------------------------

data RecursiveTransportRequiresLowerCarrierRebuild : Set where

data RecursiveFusionCreatesIndependentSemanticAuthority : Set where

data RecursiveTransportRequiresPerHopGlobalLookup : Set where

recursiveTransportNeedNotRebuildLowerCarrier :
  RecursiveTransportRequiresLowerCarrierRebuild → ⊥
recursiveTransportNeedNotRebuildLowerCarrier ()

recursiveFusionDoesNotCreateSecondAuthority :
  RecursiveFusionCreatesIndependentSemanticAuthority → ⊥
recursiveFusionDoesNotCreateSecondAuthority ()

recursiveTransportNeedNotPerformGlobalLookupPerHop :
  RecursiveTransportRequiresPerHopGlobalLookup → ⊥
recursiveTransportNeedNotPerformGlobalLookupPerHop ()
