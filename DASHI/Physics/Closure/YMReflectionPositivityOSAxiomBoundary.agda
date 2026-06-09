module DASHI.Physics.Closure.YMReflectionPositivityOSAxiomBoundary where

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

osAxiomText : String
osAxiomText =
  "<O^dagger theta* O> = integral |F[A+,A0]|^2 exp(-S+[A+]-S0[A0]) >= 0"

data YMReflectionPositivityOSAxiomClause : Set where
  actionSplitConsumed : YMReflectionPositivityOSAxiomClause
  transferMatrixHermitianConsumed : YMReflectionPositivityOSAxiomClause
  negativeHalfIntegratedOutByThetaChangeOfVariables :
    YMReflectionPositivityOSAxiomClause
  modulusSquaredIntegrandRecorded : YMReflectionPositivityOSAxiomClause
  positiveWeightRecorded : YMReflectionPositivityOSAxiomClause
  os0ToOs4SatisfiedRecorded : YMReflectionPositivityOSAxiomClause
  osReconstructionRouteRecorded : YMReflectionPositivityOSAxiomClause

canonicalYMReflectionPositivityOSAxiomClauses :
  List YMReflectionPositivityOSAxiomClause
canonicalYMReflectionPositivityOSAxiomClauses =
  actionSplitConsumed
  ∷ transferMatrixHermitianConsumed
  ∷ negativeHalfIntegratedOutByThetaChangeOfVariables
  ∷ modulusSquaredIntegrandRecorded
  ∷ positiveWeightRecorded
  ∷ os0ToOs4SatisfiedRecorded
  ∷ osReconstructionRouteRecorded
  ∷ []

ymReflectionPositivityOSAxiomClauseCount : Nat
ymReflectionPositivityOSAxiomClauseCount =
  listLength canonicalYMReflectionPositivityOSAxiomClauses

ymReflectionPositivityOSAxiomClauseCountIs7 :
  ymReflectionPositivityOSAxiomClauseCount ≡ 7
ymReflectionPositivityOSAxiomClauseCountIs7 = refl

data YMReflectionPositivityOSAxiomBlocker : Set where
  blocker-changeOfVariablesProofStillOpen :
    YMReflectionPositivityOSAxiomBlocker
  blocker-structuralOsPositivityProofStillOpen :
    YMReflectionPositivityOSAxiomBlocker
  blocker-osWightmanAuthorityStillOpen : YMReflectionPositivityOSAxiomBlocker
  blocker-finalContinuumAuthorityStillOpen :
    YMReflectionPositivityOSAxiomBlocker
  blocker-ymClayPromotionForbidden : YMReflectionPositivityOSAxiomBlocker

canonicalYMReflectionPositivityOSAxiomBlockers :
  List YMReflectionPositivityOSAxiomBlocker
canonicalYMReflectionPositivityOSAxiomBlockers =
  blocker-changeOfVariablesProofStillOpen
  ∷ blocker-structuralOsPositivityProofStillOpen
  ∷ blocker-osWightmanAuthorityStillOpen
  ∷ blocker-finalContinuumAuthorityStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMReflectionPositivityOSAxiomRecorded : Bool
YMReflectionPositivityOSAxiomRecorded = true

YMReflectionPositivityOSAxiomProved : Bool
YMReflectionPositivityOSAxiomProved = false

record YMReflectionPositivityOSAxiomBoundary : Set where
  field
    clauses : List YMReflectionPositivityOSAxiomClause
    clausesCanonical : clauses ≡ canonicalYMReflectionPositivityOSAxiomClauses
    blockers : List YMReflectionPositivityOSAxiomBlocker
    blockersCanonical : blockers ≡ canonicalYMReflectionPositivityOSAxiomBlockers
    clauseCountIs7 : ymReflectionPositivityOSAxiomClauseCount ≡ 7
    theoremStillFalse : YMReflectionPositivityOSAxiomProved ≡ false

canonicalYMReflectionPositivityOSAxiomBoundary :
  YMReflectionPositivityOSAxiomBoundary
canonicalYMReflectionPositivityOSAxiomBoundary =
  record
    { clauses = canonicalYMReflectionPositivityOSAxiomClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMReflectionPositivityOSAxiomBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    }

YMReflectionPositivityOSAxiomRecordedIsTrue :
  YMReflectionPositivityOSAxiomRecorded ≡ true
YMReflectionPositivityOSAxiomRecordedIsTrue = refl
