module DASHI.Physics.Closure.YMHolonomyPositivePartToSpectralMarginCompositeLightweightBoundary where

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

data YMSpectralMarginClause : Set where
  dominationPreconditionImported : YMSpectralMarginClause
  positiveHolonomyActionImported : YMSpectralMarginClause
  finiteGapSocketRecorded : YMSpectralMarginClause
  boundarySensitivityBudgetRecorded : YMSpectralMarginClause
  continuumBridgeConsumerReady : YMSpectralMarginClause
  clayPromotionStillBlocked : YMSpectralMarginClause

canonicalYMSpectralMarginClauses : List YMSpectralMarginClause
canonicalYMSpectralMarginClauses =
  dominationPreconditionImported
  ∷ positiveHolonomyActionImported
  ∷ finiteGapSocketRecorded
  ∷ boundarySensitivityBudgetRecorded
  ∷ continuumBridgeConsumerReady
  ∷ clayPromotionStillBlocked
  ∷ []

ymSpectralMarginClauseCount : Nat
ymSpectralMarginClauseCount = listLength canonicalYMSpectralMarginClauses

ymSpectralMarginClauseCountIs6 : ymSpectralMarginClauseCount ≡ 6
ymSpectralMarginClauseCountIs6 = refl

data YMSpectralMarginBlocker : Set where
  blocker-finiteGapProofStillOpen : YMSpectralMarginBlocker
  blocker-continuumTransferStillOpen : YMSpectralMarginBlocker
  blocker-nospectralpollutionStillOpen : YMSpectralMarginBlocker
  blocker-ymClayPromotionForbidden : YMSpectralMarginBlocker

canonicalYMSpectralMarginBlockers : List YMSpectralMarginBlocker
canonicalYMSpectralMarginBlockers =
  blocker-finiteGapProofStillOpen
  ∷ blocker-continuumTransferStillOpen
  ∷ blocker-nospectralpollutionStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMHolonomyPositivePartToSpectralMarginCompositeRecorded : Bool
YMHolonomyPositivePartToSpectralMarginCompositeRecorded = true

YMHolonomyPositivePartToSpectralMarginCompositeProved : Bool
YMHolonomyPositivePartToSpectralMarginCompositeProved = false

record YMHolonomyPositivePartToSpectralMarginCompositeLightweightBoundary : Set where
  field
    clauses : List YMSpectralMarginClause
    clausesCanonical : clauses ≡ canonicalYMSpectralMarginClauses
    blockers : List YMSpectralMarginBlocker
    blockersCanonical : blockers ≡ canonicalYMSpectralMarginBlockers
    clauseCountIs6 : ymSpectralMarginClauseCount ≡ 6
    provedStillFalse :
      YMHolonomyPositivePartToSpectralMarginCompositeProved ≡ false

canonicalYMHolonomyPositivePartToSpectralMarginCompositeLightweightBoundary :
  YMHolonomyPositivePartToSpectralMarginCompositeLightweightBoundary
canonicalYMHolonomyPositivePartToSpectralMarginCompositeLightweightBoundary =
  record
    { clauses = canonicalYMSpectralMarginClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMSpectralMarginBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

YMHolonomyPositivePartToSpectralMarginCompositeRecordedIsTrue :
  YMHolonomyPositivePartToSpectralMarginCompositeRecorded ≡ true
YMHolonomyPositivePartToSpectralMarginCompositeRecordedIsTrue = refl
