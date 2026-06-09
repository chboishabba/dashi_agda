module DASHI.Physics.Closure.UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary where

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

data UJvNSocketClause : Set where
  parallelogramSocketImported : UJvNSocketClause
  jordanVonNeumannAdapterImported : UJvNSocketClause
  quadraticEmergenceSocketRecorded : UJvNSocketClause
  signatureConsumerStillBlocked : UJvNSocketClause
  cliffordConsumerStillBlocked : UJvNSocketClause
  terminalPromotionStillBlocked : UJvNSocketClause

canonicalUJvNSocketClauses : List UJvNSocketClause
canonicalUJvNSocketClauses =
  parallelogramSocketImported
  ∷ jordanVonNeumannAdapterImported
  ∷ quadraticEmergenceSocketRecorded
  ∷ signatureConsumerStillBlocked
  ∷ cliffordConsumerStillBlocked
  ∷ terminalPromotionStillBlocked
  ∷ []

uJvNSocketClauseCount : Nat
uJvNSocketClauseCount = listLength canonicalUJvNSocketClauses

uJvNSocketClauseCountIs6 : uJvNSocketClauseCount ≡ 6
uJvNSocketClauseCountIs6 = refl

data UJvNSocketBlocker : Set where
  blocker-jordanVonNeumannTheoremStillOpen : UJvNSocketBlocker
  blocker-signatureStillOpen : UJvNSocketBlocker
  blocker-cliffordStillOpen : UJvNSocketBlocker
  blocker-terminalPromotionForbidden : UJvNSocketBlocker

canonicalUJvNSocketBlockers : List UJvNSocketBlocker
canonicalUJvNSocketBlockers =
  blocker-jordanVonNeumannTheoremStillOpen
  ∷ blocker-signatureStillOpen
  ∷ blocker-cliffordStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ []

UnificationParallelogramToJordanVonNeumannSocketCompositeRecorded : Bool
UnificationParallelogramToJordanVonNeumannSocketCompositeRecorded = true

UnificationParallelogramToJordanVonNeumannSocketCompositeProved : Bool
UnificationParallelogramToJordanVonNeumannSocketCompositeProved = false

record UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary : Set where
  field
    clauses : List UJvNSocketClause
    clausesCanonical : clauses ≡ canonicalUJvNSocketClauses
    blockers : List UJvNSocketBlocker
    blockersCanonical : blockers ≡ canonicalUJvNSocketBlockers
    clauseCountIs6 : uJvNSocketClauseCount ≡ 6
    provedStillFalse :
      UnificationParallelogramToJordanVonNeumannSocketCompositeProved ≡ false

canonicalUnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary :
  UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary
canonicalUnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary =
  record
    { clauses = canonicalUJvNSocketClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUJvNSocketBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

UnificationParallelogramToJordanVonNeumannSocketCompositeRecordedIsTrue :
  UnificationParallelogramToJordanVonNeumannSocketCompositeRecorded ≡ true
UnificationParallelogramToJordanVonNeumannSocketCompositeRecordedIsTrue = refl
