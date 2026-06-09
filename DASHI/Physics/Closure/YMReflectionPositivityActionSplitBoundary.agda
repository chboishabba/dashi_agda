module DASHI.Physics.Closure.YMReflectionPositivityActionSplitBoundary where

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

actionSplitText : String
actionSplitText =
  "S[A] = S_+[A] + S_0[A] + S_-[A] with S_+[theta*A] = S_-[A] and S_0[theta*A] = S_0[A]"

data YMReflectionPositivityActionSplitClause : Set where
  positiveTimePlaquetteSectorRecorded : YMReflectionPositivityActionSplitClause
  zeroTimePlaquetteSectorRecorded : YMReflectionPositivityActionSplitClause
  negativeTimePlaquetteSectorRecorded : YMReflectionPositivityActionSplitClause
  thetaSwapsPositiveAndNegativeRecorded : YMReflectionPositivityActionSplitClause
  thetaFixesZeroSectorRecorded : YMReflectionPositivityActionSplitClause
  exactActionInvarianceRecorded : YMReflectionPositivityActionSplitClause

canonicalYMReflectionPositivityActionSplitClauses :
  List YMReflectionPositivityActionSplitClause
canonicalYMReflectionPositivityActionSplitClauses =
  positiveTimePlaquetteSectorRecorded
  ∷ zeroTimePlaquetteSectorRecorded
  ∷ negativeTimePlaquetteSectorRecorded
  ∷ thetaSwapsPositiveAndNegativeRecorded
  ∷ thetaFixesZeroSectorRecorded
  ∷ exactActionInvarianceRecorded
  ∷ []

ymReflectionPositivityActionSplitClauseCount : Nat
ymReflectionPositivityActionSplitClauseCount =
  listLength canonicalYMReflectionPositivityActionSplitClauses

ymReflectionPositivityActionSplitClauseCountIs6 :
  ymReflectionPositivityActionSplitClauseCount ≡ 6
ymReflectionPositivityActionSplitClauseCountIs6 = refl

data YMReflectionPositivityActionSplitBlocker : Set where
  blocker-sectorDecompositionProofStillOpen :
    YMReflectionPositivityActionSplitBlocker
  blocker-thetaExchangeProofStillOpen :
    YMReflectionPositivityActionSplitBlocker
  blocker-osAxiomStillOpen : YMReflectionPositivityActionSplitBlocker
  blocker-ymClayPromotionForbidden : YMReflectionPositivityActionSplitBlocker

canonicalYMReflectionPositivityActionSplitBlockers :
  List YMReflectionPositivityActionSplitBlocker
canonicalYMReflectionPositivityActionSplitBlockers =
  blocker-sectorDecompositionProofStillOpen
  ∷ blocker-thetaExchangeProofStillOpen
  ∷ blocker-osAxiomStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMReflectionPositivityActionSplitRecorded : Bool
YMReflectionPositivityActionSplitRecorded = true

YMReflectionPositivityActionSplitProved : Bool
YMReflectionPositivityActionSplitProved = false

record YMReflectionPositivityActionSplitBoundary : Set where
  field
    clauses : List YMReflectionPositivityActionSplitClause
    clausesCanonical : clauses ≡ canonicalYMReflectionPositivityActionSplitClauses
    blockers : List YMReflectionPositivityActionSplitBlocker
    blockersCanonical : blockers ≡ canonicalYMReflectionPositivityActionSplitBlockers
    clauseCountIs6 : ymReflectionPositivityActionSplitClauseCount ≡ 6
    theoremStillFalse : YMReflectionPositivityActionSplitProved ≡ false

canonicalYMReflectionPositivityActionSplitBoundary :
  YMReflectionPositivityActionSplitBoundary
canonicalYMReflectionPositivityActionSplitBoundary =
  record
    { clauses = canonicalYMReflectionPositivityActionSplitClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMReflectionPositivityActionSplitBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; theoremStillFalse = refl
    }

YMReflectionPositivityActionSplitRecordedIsTrue :
  YMReflectionPositivityActionSplitRecorded ≡ true
YMReflectionPositivityActionSplitRecordedIsTrue = refl
