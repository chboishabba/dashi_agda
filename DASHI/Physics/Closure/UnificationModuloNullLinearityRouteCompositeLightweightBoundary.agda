module DASHI.Physics.Closure.UnificationModuloNullLinearityRouteCompositeLightweightBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data UModuloRouteClause : Set where
  hcCompositeImported : UModuloRouteClause
  nullClassStabilityImported : UModuloRouteClause
  nullTransportImported : UModuloRouteClause
  representativeIndependenceLifted : UModuloRouteClause
  quotientLinearityRouteRecorded : UModuloRouteClause
  fourPointConsumerReady : UModuloRouteClause

canonicalUModuloRouteClauses : List UModuloRouteClause
canonicalUModuloRouteClauses =
  hcCompositeImported
  ∷ nullClassStabilityImported
  ∷ nullTransportImported
  ∷ representativeIndependenceLifted
  ∷ quotientLinearityRouteRecorded
  ∷ fourPointConsumerReady
  ∷ []

uModuloRouteClauseCount : Nat
uModuloRouteClauseCount = listLength canonicalUModuloRouteClauses

uModuloRouteClauseCountIs6 : uModuloRouteClauseCount ≡ 6
uModuloRouteClauseCountIs6 = refl

data UModuloRouteBlocker : Set where
  blocker-moduloNullLinearityTheoremStillOpen : UModuloRouteBlocker
  blocker-fourPointStillOpen : UModuloRouteBlocker
  blocker-parallelogramStillOpen : UModuloRouteBlocker
  blocker-terminalPromotionForbidden : UModuloRouteBlocker

canonicalUModuloRouteBlockers : List UModuloRouteBlocker
canonicalUModuloRouteBlockers =
  blocker-moduloNullLinearityTheoremStillOpen
  ∷ blocker-fourPointStillOpen
  ∷ blocker-parallelogramStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ []

UnificationModuloNullLinearityRouteCompositeRecorded : Bool
UnificationModuloNullLinearityRouteCompositeRecorded = true

UnificationModuloNullLinearityRouteCompositeProved : Bool
UnificationModuloNullLinearityRouteCompositeProved = false

record UnificationModuloNullLinearityRouteCompositeLightweightBoundary : Set where
  field
    clauses : List UModuloRouteClause
    clausesCanonical : clauses ≡ canonicalUModuloRouteClauses
    blockers : List UModuloRouteBlocker
    blockersCanonical : blockers ≡ canonicalUModuloRouteBlockers
    clauseCountIs6 : uModuloRouteClauseCount ≡ 6
    provedStillFalse :
      UnificationModuloNullLinearityRouteCompositeProved ≡ false

canonicalUnificationModuloNullLinearityRouteCompositeLightweightBoundary :
  UnificationModuloNullLinearityRouteCompositeLightweightBoundary
canonicalUnificationModuloNullLinearityRouteCompositeLightweightBoundary =
  record
    { clauses = canonicalUModuloRouteClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUModuloRouteBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

UnificationModuloNullLinearityRouteCompositeRecordedIsTrue :
  UnificationModuloNullLinearityRouteCompositeRecorded ≡ true
UnificationModuloNullLinearityRouteCompositeRecordedIsTrue = refl
