module DASHI.Physics.Closure.YMReflectionPositivityTransferMatrixHermitianBoundary where

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

boundaryConditionText : String
boundaryConditionText =
  "(theta*A)(tau(sigma)) = -(theta*A)(sigma), so theta*A satisfies the same opposite-face boundary convention"

transferMatrixText : String
transferMatrixText =
  "theta*T = T* because theta swaps t->t+1 with t+1->t and the boundary convention introduces no phase"

data YMReflectionPositivityTransferMatrixClause : Set where
  boundaryConditionPreservedUnderThetaRecorded :
    YMReflectionPositivityTransferMatrixClause
  tauThetaCommutativityConsumed : YMReflectionPositivityTransferMatrixClause
  oppositeFaceBoundaryConventionReused :
    YMReflectionPositivityTransferMatrixClause
  noBoundaryPhaseRecorded : YMReflectionPositivityTransferMatrixClause
  transferMatrixHermitianUnderThetaRecorded :
    YMReflectionPositivityTransferMatrixClause
  osPositivityInputRecorded : YMReflectionPositivityTransferMatrixClause

canonicalYMReflectionPositivityTransferMatrixClauses :
  List YMReflectionPositivityTransferMatrixClause
canonicalYMReflectionPositivityTransferMatrixClauses =
  boundaryConditionPreservedUnderThetaRecorded
  ∷ tauThetaCommutativityConsumed
  ∷ oppositeFaceBoundaryConventionReused
  ∷ noBoundaryPhaseRecorded
  ∷ transferMatrixHermitianUnderThetaRecorded
  ∷ osPositivityInputRecorded
  ∷ []

ymReflectionPositivityTransferMatrixClauseCount : Nat
ymReflectionPositivityTransferMatrixClauseCount =
  listLength canonicalYMReflectionPositivityTransferMatrixClauses

ymReflectionPositivityTransferMatrixClauseCountIs6 :
  ymReflectionPositivityTransferMatrixClauseCount ≡ 6
ymReflectionPositivityTransferMatrixClauseCountIs6 = refl

data YMReflectionPositivityTransferMatrixBlocker : Set where
  blocker-boundaryPreservationProofStillOpen :
    YMReflectionPositivityTransferMatrixBlocker
  blocker-transferMatrixHermitianProofStillOpen :
    YMReflectionPositivityTransferMatrixBlocker
  blocker-osAxiomStillOpen : YMReflectionPositivityTransferMatrixBlocker
  blocker-ymClayPromotionForbidden : YMReflectionPositivityTransferMatrixBlocker

canonicalYMReflectionPositivityTransferMatrixBlockers :
  List YMReflectionPositivityTransferMatrixBlocker
canonicalYMReflectionPositivityTransferMatrixBlockers =
  blocker-boundaryPreservationProofStillOpen
  ∷ blocker-transferMatrixHermitianProofStillOpen
  ∷ blocker-osAxiomStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMReflectionPositivityTransferMatrixHermitianRecorded : Bool
YMReflectionPositivityTransferMatrixHermitianRecorded = true

YMReflectionPositivityTransferMatrixHermitianProved : Bool
YMReflectionPositivityTransferMatrixHermitianProved = false

record YMReflectionPositivityTransferMatrixHermitianBoundary : Set where
  field
    clauses : List YMReflectionPositivityTransferMatrixClause
    clausesCanonical :
      clauses ≡ canonicalYMReflectionPositivityTransferMatrixClauses
    blockers : List YMReflectionPositivityTransferMatrixBlocker
    blockersCanonical :
      blockers ≡ canonicalYMReflectionPositivityTransferMatrixBlockers
    clauseCountIs6 : ymReflectionPositivityTransferMatrixClauseCount ≡ 6
    theoremStillFalse :
      YMReflectionPositivityTransferMatrixHermitianProved ≡ false

canonicalYMReflectionPositivityTransferMatrixHermitianBoundary :
  YMReflectionPositivityTransferMatrixHermitianBoundary
canonicalYMReflectionPositivityTransferMatrixHermitianBoundary =
  record
    { clauses = canonicalYMReflectionPositivityTransferMatrixClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMReflectionPositivityTransferMatrixBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; theoremStillFalse = refl
    }

YMReflectionPositivityTransferMatrixHermitianRecordedIsTrue :
  YMReflectionPositivityTransferMatrixHermitianRecorded ≡ true
YMReflectionPositivityTransferMatrixHermitianRecordedIsTrue = refl
