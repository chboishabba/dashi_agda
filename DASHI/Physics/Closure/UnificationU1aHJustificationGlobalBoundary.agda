module DASHI.Physics.Closure.UnificationU1aHJustificationGlobalBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

globalU1aHText : String
globalU1aHText =
  "For any Hilbert space H, G(s)=||s||^2_H and B=Re<.,.> give the Jordan-von Neumann setting directly"

data UnificationU1aHGlobalClause : Set where
  hilbertNormSquareRecorded : UnificationU1aHGlobalClause
  realPartInnerProductRecorded : UnificationU1aHGlobalClause
  bilinearCrossTermRecorded : UnificationU1aHGlobalClause
  positivityRecorded : UnificationU1aHGlobalClause
  jordanVonNeumannSettingRecorded : UnificationU1aHGlobalClause

canonicalUnificationU1aHGlobalClauses : List UnificationU1aHGlobalClause
canonicalUnificationU1aHGlobalClauses =
  hilbertNormSquareRecorded
  ∷ realPartInnerProductRecorded
  ∷ bilinearCrossTermRecorded
  ∷ positivityRecorded
  ∷ jordanVonNeumannSettingRecorded
  ∷ []

unificationU1aHGlobalClauseCount : Nat
unificationU1aHGlobalClauseCount =
  listLength canonicalUnificationU1aHGlobalClauses

unificationU1aHGlobalClauseCountIs5 :
  unificationU1aHGlobalClauseCount ≡ 5
unificationU1aHGlobalClauseCountIs5 = refl

data UnificationU1aHGlobalBlocker : Set where
  blocker-laneSpecializationStillOpen : UnificationU1aHGlobalBlocker
  blocker-signatureConsumerStillOpen : UnificationU1aHGlobalBlocker
  blocker-unificationPromotionForbidden : UnificationU1aHGlobalBlocker

canonicalUnificationU1aHGlobalBlockers : List UnificationU1aHGlobalBlocker
canonicalUnificationU1aHGlobalBlockers =
  blocker-laneSpecializationStillOpen
  ∷ blocker-signatureConsumerStillOpen
  ∷ blocker-unificationPromotionForbidden
  ∷ []

UnificationU1aHJustificationGlobalRecorded : Bool
UnificationU1aHJustificationGlobalRecorded = true

UnificationU1aHJustificationGlobalProved : Bool
UnificationU1aHJustificationGlobalProved = false

record UnificationU1aHJustificationGlobalBoundary : Set where
  field
    clauses : List UnificationU1aHGlobalClause
    clausesCanonical : clauses ≡ canonicalUnificationU1aHGlobalClauses
    blockers : List UnificationU1aHGlobalBlocker
    blockersCanonical : blockers ≡ canonicalUnificationU1aHGlobalBlockers
    clauseCountIs5 : unificationU1aHGlobalClauseCount ≡ 5
    theoremStillFalse : UnificationU1aHJustificationGlobalProved ≡ false

canonicalUnificationU1aHJustificationGlobalBoundary :
  UnificationU1aHJustificationGlobalBoundary
canonicalUnificationU1aHJustificationGlobalBoundary =
  record
    { clauses = canonicalUnificationU1aHGlobalClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUnificationU1aHGlobalBlockers
    ; blockersCanonical = refl
    ; clauseCountIs5 = refl
    ; theoremStillFalse = refl
    }

UnificationU1aHJustificationGlobalRecordedIsTrue :
  UnificationU1aHJustificationGlobalRecorded ≡ true
UnificationU1aHJustificationGlobalRecordedIsTrue = refl
