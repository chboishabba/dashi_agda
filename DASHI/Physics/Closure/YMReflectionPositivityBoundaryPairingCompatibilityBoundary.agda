module DASHI.Physics.Closure.YMReflectionPositivityBoundaryPairingCompatibilityBoundary where

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

data YMBoundaryPairingClause : Set where
  tauSpatialBoundaryConsumed : YMBoundaryPairingClause
  thetaReflectionBoundaryConsumed : YMBoundaryPairingClause
  oppositeFacePairsPreservedUnderThetaRecorded : YMBoundaryPairingClause
  boundaryPairingCompatibleWithRPRecorded : YMBoundaryPairingClause
  osInputRouteFedOnlyAfterCompatibility : YMBoundaryPairingClause

canonicalYMBoundaryPairingClauses : List YMBoundaryPairingClause
canonicalYMBoundaryPairingClauses =
  tauSpatialBoundaryConsumed
  ∷ thetaReflectionBoundaryConsumed
  ∷ oppositeFacePairsPreservedUnderThetaRecorded
  ∷ boundaryPairingCompatibleWithRPRecorded
  ∷ osInputRouteFedOnlyAfterCompatibility
  ∷ []

ymBoundaryPairingClauseCount : Nat
ymBoundaryPairingClauseCount = listLength canonicalYMBoundaryPairingClauses

ymBoundaryPairingClauseCountIs5 : ymBoundaryPairingClauseCount ≡ 5
ymBoundaryPairingClauseCountIs5 = refl

data YMBoundaryPairingBlocker : Set where
  blocker-tauSpatialBoundaryStillOpen : YMBoundaryPairingBlocker
  blocker-thetaBoundaryStillOpen : YMBoundaryPairingBlocker
  blocker-pairingCompatibilityProofOpen : YMBoundaryPairingBlocker
  blocker-reflectionPositivityStillOpen : YMBoundaryPairingBlocker
  blocker-ymClayPromotionForbidden : YMBoundaryPairingBlocker

canonicalYMBoundaryPairingBlockers : List YMBoundaryPairingBlocker
canonicalYMBoundaryPairingBlockers =
  blocker-tauSpatialBoundaryStillOpen
  ∷ blocker-thetaBoundaryStillOpen
  ∷ blocker-pairingCompatibilityProofOpen
  ∷ blocker-reflectionPositivityStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMReflectionPositivityBoundaryPairingCompatibilityRecorded : Bool
YMReflectionPositivityBoundaryPairingCompatibilityRecorded = true

YMReflectionPositivityBoundaryPairingCompatibilityProved : Bool
YMReflectionPositivityBoundaryPairingCompatibilityProved = false

record YMReflectionPositivityBoundaryPairingCompatibilityBoundary : Set where
  field
    clauses : List YMBoundaryPairingClause
    clausesCanonical : clauses ≡ canonicalYMBoundaryPairingClauses
    blockers : List YMBoundaryPairingBlocker
    blockersCanonical : blockers ≡ canonicalYMBoundaryPairingBlockers
    clauseCountIs5 : ymBoundaryPairingClauseCount ≡ 5
    theoremStillFalse :
      YMReflectionPositivityBoundaryPairingCompatibilityProved ≡ false

canonicalYMReflectionPositivityBoundaryPairingCompatibilityBoundary :
  YMReflectionPositivityBoundaryPairingCompatibilityBoundary
canonicalYMReflectionPositivityBoundaryPairingCompatibilityBoundary =
  record
    { clauses = canonicalYMBoundaryPairingClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMBoundaryPairingBlockers
    ; blockersCanonical = refl
    ; clauseCountIs5 = refl
    ; theoremStillFalse = refl
    }

YMReflectionPositivityBoundaryPairingCompatibilityRecordedIsTrue :
  YMReflectionPositivityBoundaryPairingCompatibilityRecorded ≡ true
YMReflectionPositivityBoundaryPairingCompatibilityRecordedIsTrue = refl
