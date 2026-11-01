module DASHI.Physics.Closure.UnificationFourPointToParallelogramSocketCompositeLightweightBoundary where

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

data UParallelogramSocketClause : Set where
  fourPointRouteImported : UParallelogramSocketClause
  hcSpecializationImported : UParallelogramSocketClause
  quotientLinearityImported : UParallelogramSocketClause
  parallelogramSocketRecorded : UParallelogramSocketClause
  badFamilyExclusionRetained : UParallelogramSocketClause
  jordanVonNeumannStillBlocked : UParallelogramSocketClause

canonicalUParallelogramSocketClauses : List UParallelogramSocketClause
canonicalUParallelogramSocketClauses =
  fourPointRouteImported
  ∷ hcSpecializationImported
  ∷ quotientLinearityImported
  ∷ parallelogramSocketRecorded
  ∷ badFamilyExclusionRetained
  ∷ jordanVonNeumannStillBlocked
  ∷ []

uParallelogramSocketClauseCount : Nat
uParallelogramSocketClauseCount = listLength canonicalUParallelogramSocketClauses

uParallelogramSocketClauseCountIs6 : uParallelogramSocketClauseCount ≡ 6
uParallelogramSocketClauseCountIs6 = refl

data UParallelogramSocketBlocker : Set where
  blocker-parallelogramTheoremStillOpen : UParallelogramSocketBlocker
  blocker-jordanVonNeumannStillOpen : UParallelogramSocketBlocker
  blocker-signatureStillOpen : UParallelogramSocketBlocker
  blocker-terminalPromotionForbidden : UParallelogramSocketBlocker

canonicalUParallelogramSocketBlockers : List UParallelogramSocketBlocker
canonicalUParallelogramSocketBlockers =
  blocker-parallelogramTheoremStillOpen
  ∷ blocker-jordanVonNeumannStillOpen
  ∷ blocker-signatureStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ []

UnificationFourPointToParallelogramSocketCompositeRecorded : Bool
UnificationFourPointToParallelogramSocketCompositeRecorded = true

UnificationFourPointToParallelogramSocketCompositeProved : Bool
UnificationFourPointToParallelogramSocketCompositeProved = false

record UnificationFourPointToParallelogramSocketCompositeLightweightBoundary : Set where
  field
    clauses : List UParallelogramSocketClause
    clausesCanonical : clauses ≡ canonicalUParallelogramSocketClauses
    blockers : List UParallelogramSocketBlocker
    blockersCanonical : blockers ≡ canonicalUParallelogramSocketBlockers
    clauseCountIs6 : uParallelogramSocketClauseCount ≡ 6
    provedStillFalse :
      UnificationFourPointToParallelogramSocketCompositeProved ≡ false

canonicalUnificationFourPointToParallelogramSocketCompositeLightweightBoundary :
  UnificationFourPointToParallelogramSocketCompositeLightweightBoundary
canonicalUnificationFourPointToParallelogramSocketCompositeLightweightBoundary =
  record
    { clauses = canonicalUParallelogramSocketClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUParallelogramSocketBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

UnificationFourPointToParallelogramSocketCompositeRecordedIsTrue :
  UnificationFourPointToParallelogramSocketCompositeRecorded ≡ true
UnificationFourPointToParallelogramSocketCompositeRecordedIsTrue = refl
