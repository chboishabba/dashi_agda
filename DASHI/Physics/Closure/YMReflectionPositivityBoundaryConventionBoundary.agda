module DASHI.Physics.Closure.YMReflectionPositivityBoundaryConventionBoundary where

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

reflectionCompatibilityText : String
reflectionCompatibilityText =
  "tau acts on spatial indices only, so opposite-face pairing is compatible with Euclidean time reflection theta"

data YMReflectionPositivityClause : Set where
  oppositeFaceBoundaryConventionConsumed : YMReflectionPositivityClause
  spatialOnlyTauActionRecorded : YMReflectionPositivityClause
  euclideanTimeReflectionThetaRecorded : YMReflectionPositivityClause
  boundaryPairingCompatibleWithThetaRecorded : YMReflectionPositivityClause
  osReflectionPositivityInputRecorded : YMReflectionPositivityClause
  osWightmanRouteFedOnlyAfterRP : YMReflectionPositivityClause
  clayPromotionStillBlocked : YMReflectionPositivityClause

canonicalYMReflectionPositivityClauses : List YMReflectionPositivityClause
canonicalYMReflectionPositivityClauses =
  oppositeFaceBoundaryConventionConsumed
  ∷ spatialOnlyTauActionRecorded
  ∷ euclideanTimeReflectionThetaRecorded
  ∷ boundaryPairingCompatibleWithThetaRecorded
  ∷ osReflectionPositivityInputRecorded
  ∷ osWightmanRouteFedOnlyAfterRP
  ∷ clayPromotionStillBlocked
  ∷ []

ymReflectionPositivityClauseCount : Nat
ymReflectionPositivityClauseCount = listLength canonicalYMReflectionPositivityClauses

ymReflectionPositivityClauseCountIs7 : ymReflectionPositivityClauseCount ≡ 7
ymReflectionPositivityClauseCountIs7 = refl

data YMReflectionPositivityBlocker : Set where
  blocker-spatialTauCompatibilityProofOpen : YMReflectionPositivityBlocker
  blocker-osReflectionPositivityProofOpen : YMReflectionPositivityBlocker
  blocker-osWightmanAuthorityStillOpen : YMReflectionPositivityBlocker
  blocker-finalContinuumMassGapStillOpen : YMReflectionPositivityBlocker
  blocker-ymClayPromotionForbidden : YMReflectionPositivityBlocker

canonicalYMReflectionPositivityBlockers : List YMReflectionPositivityBlocker
canonicalYMReflectionPositivityBlockers =
  blocker-spatialTauCompatibilityProofOpen
  ∷ blocker-osReflectionPositivityProofOpen
  ∷ blocker-osWightmanAuthorityStillOpen
  ∷ blocker-finalContinuumMassGapStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMReflectionPositivityBoundaryConventionRecorded : Bool
YMReflectionPositivityBoundaryConventionRecorded = true

YMReflectionPositivityBoundaryConventionProved : Bool
YMReflectionPositivityBoundaryConventionProved = false

record YMReflectionPositivityBoundaryConventionBoundary : Set where
  field
    clauses : List YMReflectionPositivityClause
    clausesCanonical : clauses ≡ canonicalYMReflectionPositivityClauses
    blockers : List YMReflectionPositivityBlocker
    blockersCanonical : blockers ≡ canonicalYMReflectionPositivityBlockers
    clauseCountIs7 : ymReflectionPositivityClauseCount ≡ 7
    theoremStillFalse :
      YMReflectionPositivityBoundaryConventionProved ≡ false

canonicalYMReflectionPositivityBoundaryConventionBoundary :
  YMReflectionPositivityBoundaryConventionBoundary
canonicalYMReflectionPositivityBoundaryConventionBoundary =
  record
    { clauses = canonicalYMReflectionPositivityClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMReflectionPositivityBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    }

YMReflectionPositivityBoundaryConventionRecordedIsTrue :
  YMReflectionPositivityBoundaryConventionRecorded ≡ true
YMReflectionPositivityBoundaryConventionRecordedIsTrue = refl
