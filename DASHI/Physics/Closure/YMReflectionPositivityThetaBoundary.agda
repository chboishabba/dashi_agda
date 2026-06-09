module DASHI.Physics.Closure.YMReflectionPositivityThetaBoundary where

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

data YMThetaClause : Set where
  euclideanTimeReflectionRecorded : YMThetaClause
  positiveTimeHalfSpaceRecorded : YMThetaClause
  thetaActsOnTemporalIndexOnlyRecorded : YMThetaClause
  osReflectionPositivityConsumerFed : YMThetaClause

canonicalYMThetaClauses : List YMThetaClause
canonicalYMThetaClauses =
  euclideanTimeReflectionRecorded
  ∷ positiveTimeHalfSpaceRecorded
  ∷ thetaActsOnTemporalIndexOnlyRecorded
  ∷ osReflectionPositivityConsumerFed
  ∷ []

ymThetaClauseCount : Nat
ymThetaClauseCount = listLength canonicalYMThetaClauses

ymThetaClauseCountIs4 : ymThetaClauseCount ≡ 4
ymThetaClauseCountIs4 = refl

data YMThetaBlocker : Set where
  blocker-thetaReflectionProofOpen : YMThetaBlocker
  blocker-positiveTimeHalfSpaceProofOpen : YMThetaBlocker
  blocker-osReflectionPositivityStillOpen : YMThetaBlocker
  blocker-ymClayPromotionForbidden : YMThetaBlocker

canonicalYMThetaBlockers : List YMThetaBlocker
canonicalYMThetaBlockers =
  blocker-thetaReflectionProofOpen
  ∷ blocker-positiveTimeHalfSpaceProofOpen
  ∷ blocker-osReflectionPositivityStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMReflectionPositivityThetaRecorded : Bool
YMReflectionPositivityThetaRecorded = true

YMReflectionPositivityThetaProved : Bool
YMReflectionPositivityThetaProved = false

record YMReflectionPositivityThetaBoundary : Set where
  field
    clauses : List YMThetaClause
    clausesCanonical : clauses ≡ canonicalYMThetaClauses
    blockers : List YMThetaBlocker
    blockersCanonical : blockers ≡ canonicalYMThetaBlockers
    clauseCountIs4 : ymThetaClauseCount ≡ 4
    theoremStillFalse : YMReflectionPositivityThetaProved ≡ false

canonicalYMReflectionPositivityThetaBoundary :
  YMReflectionPositivityThetaBoundary
canonicalYMReflectionPositivityThetaBoundary =
  record
    { clauses = canonicalYMThetaClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMThetaBlockers
    ; blockersCanonical = refl
    ; clauseCountIs4 = refl
    ; theoremStillFalse = refl
    }

YMReflectionPositivityThetaRecordedIsTrue :
  YMReflectionPositivityThetaRecorded ≡ true
YMReflectionPositivityThetaRecordedIsTrue = refl
