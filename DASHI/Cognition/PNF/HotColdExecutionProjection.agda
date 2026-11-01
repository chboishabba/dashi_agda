module DASHI.Cognition.PNF.HotColdExecutionProjection where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Append-only semantic history versus rebuildable hot current state.
--
-- History is the provenance authority.  The hot projection may be maintained
-- transactionally for speed, but it must be rebuildable from history and cannot
-- manufacture semantic facts absent from that history.
------------------------------------------------------------------------

record HotColdProjection (History Hot : Set) : Set where
  constructor hotColdProjection
  field
    rebuildCurrent : History → Hot
    maintainedCurrent : History → Hot
    maintainedEqualsRebuilt :
      (history : History) → maintainedCurrent history ≡ rebuildCurrent history

open HotColdProjection public

record HotStateCostReceipt : Set where
  constructor hotStateCostReceipt
  field
    historyRows : Nat
    hotRows : Nat
    currentStateLookupWork : Nat
    rebuildWork : Nat

open HotStateCostReceipt public

data HotProjectionSemanticPromotionPermission : Set where

hotProjectionCannotInventSemantics : HotProjectionSemanticPromotionPermission → ⊥
hotProjectionCannotInventSemantics ()

record HotColdBoundary : Set where
  constructor hotColdBoundary
  field
    appendOnlyHistoryIsAuthority : Bool
    appendOnlyHistoryIsAuthorityIsTrue : appendOnlyHistoryIsAuthority ≡ true
    currentHotStateMayBeMaterialized : Bool
    currentHotStateMayBeMaterializedIsTrue : currentHotStateMayBeMaterialized ≡ true
    materializedHotStateMustBeRebuildable : Bool
    materializedHotStateMustBeRebuildableIsTrue :
      materializedHotStateMustBeRebuildable ≡ true

open HotColdBoundary public

canonicalHotColdBoundary : HotColdBoundary
canonicalHotColdBoundary = hotColdBoundary true refl true refl true refl
