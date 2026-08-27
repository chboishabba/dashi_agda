module DASHI.Cognition.PNF.RecursiveBoundaryDeltaTransportExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.HierarchicalDeltaFusionExact as Hierarchical

------------------------------------------------------------------------
-- B2 generic hierarchy specialization.
--
-- HierarchicalDeltaFusionExact already owns the state-level theorem that a
-- fused execution must realize the same semantic state as sequential delta
-- application, and that a sufficient closed-fibre summary removes any need to
-- reopen the child carrier.  This module does not duplicate that owner.
--
-- Instead it adds the complementary delta-algebra law required for recursive
-- transport: every hierarchy level owns a delta carrier, and transport to the
-- next parent is a homomorphism of the fusion operation.  Batching before
-- transport and batching after transport are therefore observationally
-- identical at the delta boundary; Hierarchical.DeltaFusion separately governs
-- equality after those deltas are applied to semantic state.
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
-- Cross-owner boundary.
--
-- The existing hierarchical owner already proves that hierarchy depth alone
-- cannot authorize reopening descendants.  Re-export that consequence here so
-- the B2 transport contract remains explicitly attached to the established
-- no-rescan theorem rather than inventing a parallel justification.
------------------------------------------------------------------------

recursiveHierarchyDepthDoesNotAuthorizeRescan :
  Hierarchical.HierarchyDepthAuthorizesRescanPermission → ⊥
recursiveHierarchyDepthDoesNotAuthorizeRescan =
  Hierarchical.hierarchyDepthDoesNotAuthorizeRescan

------------------------------------------------------------------------
-- Negative boundaries specific to recursive transport.
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
