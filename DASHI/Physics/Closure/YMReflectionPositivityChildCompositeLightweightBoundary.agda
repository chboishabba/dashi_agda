module DASHI.Physics.Closure.YMReflectionPositivityChildCompositeLightweightBoundary where

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

data YMRPChildCompositeClause : Set where
  tauSpatialChildImported : YMRPChildCompositeClause
  thetaChildImported : YMRPChildCompositeClause
  pairingCompatibilityChildImported : YMRPChildCompositeClause
  parentReflectionPositivityBoundaryFed : YMRPChildCompositeClause
  osWightmanRouteStillBlocked : YMRPChildCompositeClause
  clayPromotionStillBlocked : YMRPChildCompositeClause

canonicalYMRPChildCompositeClauses : List YMRPChildCompositeClause
canonicalYMRPChildCompositeClauses =
  tauSpatialChildImported
  ∷ thetaChildImported
  ∷ pairingCompatibilityChildImported
  ∷ parentReflectionPositivityBoundaryFed
  ∷ osWightmanRouteStillBlocked
  ∷ clayPromotionStillBlocked
  ∷ []

ymRPChildCompositeClauseCount : Nat
ymRPChildCompositeClauseCount = listLength canonicalYMRPChildCompositeClauses

ymRPChildCompositeClauseCountIs6 : ymRPChildCompositeClauseCount ≡ 6
ymRPChildCompositeClauseCountIs6 = refl

data YMRPChildCompositeBlocker : Set where
  blocker-tauSpatialChildStillOpen : YMRPChildCompositeBlocker
  blocker-thetaChildStillOpen : YMRPChildCompositeBlocker
  blocker-pairingCompatibilityChildStillOpen : YMRPChildCompositeBlocker
  blocker-parentRPBoundaryStillOpen : YMRPChildCompositeBlocker
  blocker-ymClayPromotionForbidden : YMRPChildCompositeBlocker

canonicalYMRPChildCompositeBlockers : List YMRPChildCompositeBlocker
canonicalYMRPChildCompositeBlockers =
  blocker-tauSpatialChildStillOpen
  ∷ blocker-thetaChildStillOpen
  ∷ blocker-pairingCompatibilityChildStillOpen
  ∷ blocker-parentRPBoundaryStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMReflectionPositivityChildCompositeRecorded : Bool
YMReflectionPositivityChildCompositeRecorded = true

YMReflectionPositivityChildCompositeProved : Bool
YMReflectionPositivityChildCompositeProved = false

record YMReflectionPositivityChildCompositeLightweightBoundary : Set where
  field
    clauses : List YMRPChildCompositeClause
    clausesCanonical : clauses ≡ canonicalYMRPChildCompositeClauses
    blockers : List YMRPChildCompositeBlocker
    blockersCanonical : blockers ≡ canonicalYMRPChildCompositeBlockers
    clauseCountIs6 : ymRPChildCompositeClauseCount ≡ 6
    provedStillFalse : YMReflectionPositivityChildCompositeProved ≡ false

canonicalYMReflectionPositivityChildCompositeLightweightBoundary :
  YMReflectionPositivityChildCompositeLightweightBoundary
canonicalYMReflectionPositivityChildCompositeLightweightBoundary =
  record
    { clauses = canonicalYMRPChildCompositeClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMRPChildCompositeBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

YMReflectionPositivityChildCompositeRecordedIsTrue :
  YMReflectionPositivityChildCompositeRecorded ≡ true
YMReflectionPositivityChildCompositeRecordedIsTrue = refl
