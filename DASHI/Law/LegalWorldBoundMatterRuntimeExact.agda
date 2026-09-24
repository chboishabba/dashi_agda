module DASHI.Law.LegalWorldBoundMatterRuntimeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.LegalWorldRevisionReconstructionExact as World

------------------------------------------------------------------------
-- A MatterRuntime bound to one legal-world coordinate may change reader/view
-- state, but time or jurisdiction changes require an explicit world rebind.
------------------------------------------------------------------------

data MatterCommandKind : Set where
  selectObject : MatterCommandKind
  followTarget : MatterCommandKind
  focusProvenance : MatterCommandKind
  openSource : MatterCommandKind
  explain : MatterCommandKind
  expandExplanation : MatterCommandKind
  setProjection : MatterCommandKind
  setRange : MatterCommandKind
  setJurisdiction : MatterCommandKind
  back : MatterCommandKind

data BoundDispatchDisposition : Set where
  executeInBoundWorld : BoundDispatchDisposition
  requireWorldRebind : BoundDispatchDisposition

dispatchKind : MatterCommandKind → BoundDispatchDisposition
dispatchKind selectObject = executeInBoundWorld
dispatchKind followTarget = executeInBoundWorld
dispatchKind focusProvenance = executeInBoundWorld
dispatchKind openSource = executeInBoundWorld
dispatchKind explain = executeInBoundWorld
dispatchKind expandExplanation = executeInBoundWorld
dispatchKind setProjection = executeInBoundWorld
dispatchKind setRange = requireWorldRebind
dispatchKind setJurisdiction = requireWorldRebind
dispatchKind back = executeInBoundWorld

rangeRequiresRebind :
  dispatchKind setRange ≡ requireWorldRebind
rangeRequiresRebind = refl

jurisdictionRequiresRebind :
  dispatchKind setJurisdiction ≡ requireWorldRebind
jurisdictionRequiresRebind = refl

record LegalWorldBoundMatterRuntimeBoundary : Set where
  constructor legalWorldBoundMatterRuntimeBoundary
  field
    runtimeCarriesExplicitWorldCoordinate : Bool
    runtimeCarriesExplicitWorldCoordinateIsTrue :
      runtimeCarriesExplicitWorldCoordinate ≡ true

    ordinaryReaderCommandMayMutateBoundWorld : Bool
    ordinaryReaderCommandMayMutateBoundWorldIsFalse :
      ordinaryReaderCommandMayMutateBoundWorld ≡ false

    timeChangeRequiresExplicitWorldRebind : Bool
    timeChangeRequiresExplicitWorldRebindIsTrue :
      timeChangeRequiresExplicitWorldRebind ≡ true

    jurisdictionChangeRequiresExplicitWorldRebind : Bool
    jurisdictionChangeRequiresExplicitWorldRebindIsTrue :
      jurisdictionChangeRequiresExplicitWorldRebind ≡ true

    worldRebindCreatesSemanticAuthority : Bool
    worldRebindCreatesSemanticAuthorityIsFalse :
      worldRebindCreatesSemanticAuthority ≡ false

    worldRebindCreatesClaimTruth : Bool
    worldRebindCreatesClaimTruthIsFalse :
      worldRebindCreatesClaimTruth ≡ false

open LegalWorldBoundMatterRuntimeBoundary public

canonicalLegalWorldBoundMatterRuntimeBoundary :
  LegalWorldBoundMatterRuntimeBoundary
canonicalLegalWorldBoundMatterRuntimeBoundary =
  legalWorldBoundMatterRuntimeBoundary
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl

worldReconstructionAnchor :
  World.LegalWorldRevisionReconstructionBoundary
worldReconstructionAnchor =
  World.canonicalLegalWorldRevisionReconstructionBoundary

data ReaderCommandAutomaticallyChangesLegalWorld : Set where

readerCommandCannotAutomaticallyChangeLegalWorld :
  ReaderCommandAutomaticallyChangesLegalWorld → ⊥
readerCommandCannotAutomaticallyChangeLegalWorld ()
