module DASHI.Physics.Closure.UnificationNullClassSubspaceCompleteBoundary where

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

nullOrthogonalityText : String
nullOrthogonalityText =
  "G(n)=0 -> B(n,s)=0 for all s"

data UNullClassSubspaceClause : Set where
  discriminantBoundaryConsumed : UNullClassSubspaceClause
  nullOrthogonalityRecorded : UNullClassSubspaceClause
  nullClassClosedUnderAdditionRecorded : UNullClassSubspaceClause
  nullClassClosedUnderScalarMultiplicationRecorded : UNullClassSubspaceClause
  representativeIndependenceRecorded : UNullClassSubspaceClause
  quotientCarrierWellDefinedRecorded : UNullClassSubspaceClause
  downstreamModuloNullLinearityRouteRecorded : UNullClassSubspaceClause

canonicalUNullClassSubspaceClauses : List UNullClassSubspaceClause
canonicalUNullClassSubspaceClauses =
  discriminantBoundaryConsumed
  ∷ nullOrthogonalityRecorded
  ∷ nullClassClosedUnderAdditionRecorded
  ∷ nullClassClosedUnderScalarMultiplicationRecorded
  ∷ representativeIndependenceRecorded
  ∷ quotientCarrierWellDefinedRecorded
  ∷ downstreamModuloNullLinearityRouteRecorded
  ∷ []

uNullClassSubspaceClauseCount : Nat
uNullClassSubspaceClauseCount = listLength canonicalUNullClassSubspaceClauses

uNullClassSubspaceClauseCountIs7 : uNullClassSubspaceClauseCount ≡ 7
uNullClassSubspaceClauseCountIs7 = refl

data UNullClassSubspaceBlocker : Set where
  blocker-discriminantCrossTermTheoremStillOpen : UNullClassSubspaceBlocker
  blocker-subspaceClosureProofStillOpen : UNullClassSubspaceBlocker
  blocker-representativeIndependenceProofStillOpen : UNullClassSubspaceBlocker
  blocker-terminalPromotionForbidden : UNullClassSubspaceBlocker

canonicalUNullClassSubspaceBlockers : List UNullClassSubspaceBlocker
canonicalUNullClassSubspaceBlockers =
  blocker-discriminantCrossTermTheoremStillOpen
  ∷ blocker-subspaceClosureProofStillOpen
  ∷ blocker-representativeIndependenceProofStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ []

UnificationNullClassSubspaceCompleteRecorded : Bool
UnificationNullClassSubspaceCompleteRecorded = true

UnificationNullClassSubspaceCompleteProved : Bool
UnificationNullClassSubspaceCompleteProved = false

record UnificationNullClassSubspaceCompleteBoundary : Set where
  field
    clauses : List UNullClassSubspaceClause
    clausesCanonical : clauses ≡ canonicalUNullClassSubspaceClauses
    blockers : List UNullClassSubspaceBlocker
    blockersCanonical : blockers ≡ canonicalUNullClassSubspaceBlockers
    clauseCountIs7 : uNullClassSubspaceClauseCount ≡ 7
    theoremStillFalse :
      UnificationNullClassSubspaceCompleteProved ≡ false

canonicalUnificationNullClassSubspaceCompleteBoundary :
  UnificationNullClassSubspaceCompleteBoundary
canonicalUnificationNullClassSubspaceCompleteBoundary =
  record
    { clauses = canonicalUNullClassSubspaceClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUNullClassSubspaceBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    }

UnificationNullClassSubspaceCompleteRecordedIsTrue :
  UnificationNullClassSubspaceCompleteRecorded ≡ true
UnificationNullClassSubspaceCompleteRecordedIsTrue = refl
