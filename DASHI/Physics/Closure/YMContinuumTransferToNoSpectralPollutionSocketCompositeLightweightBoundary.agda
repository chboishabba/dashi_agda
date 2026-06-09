module DASHI.Physics.Closure.YMContinuumTransferToNoSpectralPollutionSocketCompositeLightweightBoundary where

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

data YMNoPollutionSocketClause : Set where
  continuumTransferRouteImported : YMNoPollutionSocketClause
  btToEuclideanUniversalityImported : YMNoPollutionSocketClause
  seilerCompatibilityImported : YMNoPollutionSocketClause
  noSpectralPollutionSocketRecorded : YMNoPollutionSocketClause
  wightmanConsumerStillBlocked : YMNoPollutionSocketClause
  clayPromotionStillBlocked : YMNoPollutionSocketClause

canonicalYMNoPollutionSocketClauses : List YMNoPollutionSocketClause
canonicalYMNoPollutionSocketClauses =
  continuumTransferRouteImported
  ∷ btToEuclideanUniversalityImported
  ∷ seilerCompatibilityImported
  ∷ noSpectralPollutionSocketRecorded
  ∷ wightmanConsumerStillBlocked
  ∷ clayPromotionStillBlocked
  ∷ []

ymNoPollutionSocketClauseCount : Nat
ymNoPollutionSocketClauseCount = listLength canonicalYMNoPollutionSocketClauses

ymNoPollutionSocketClauseCountIs6 : ymNoPollutionSocketClauseCount ≡ 6
ymNoPollutionSocketClauseCountIs6 = refl

data YMNoPollutionSocketBlocker : Set where
  blocker-noSpectralPollutionStillOpen : YMNoPollutionSocketBlocker
  blocker-wightmanStillOpen : YMNoPollutionSocketBlocker
  blocker-continuumMassGapStillOpen : YMNoPollutionSocketBlocker
  blocker-ymClayPromotionForbidden : YMNoPollutionSocketBlocker

canonicalYMNoPollutionSocketBlockers : List YMNoPollutionSocketBlocker
canonicalYMNoPollutionSocketBlockers =
  blocker-noSpectralPollutionStillOpen
  ∷ blocker-wightmanStillOpen
  ∷ blocker-continuumMassGapStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMContinuumTransferToNoSpectralPollutionSocketCompositeRecorded : Bool
YMContinuumTransferToNoSpectralPollutionSocketCompositeRecorded = true

YMContinuumTransferToNoSpectralPollutionSocketCompositeProved : Bool
YMContinuumTransferToNoSpectralPollutionSocketCompositeProved = false

record YMContinuumTransferToNoSpectralPollutionSocketCompositeLightweightBoundary : Set where
  field
    clauses : List YMNoPollutionSocketClause
    clausesCanonical : clauses ≡ canonicalYMNoPollutionSocketClauses
    blockers : List YMNoPollutionSocketBlocker
    blockersCanonical : blockers ≡ canonicalYMNoPollutionSocketBlockers
    clauseCountIs6 : ymNoPollutionSocketClauseCount ≡ 6
    provedStillFalse :
      YMContinuumTransferToNoSpectralPollutionSocketCompositeProved ≡ false

canonicalYMContinuumTransferToNoSpectralPollutionSocketCompositeLightweightBoundary :
  YMContinuumTransferToNoSpectralPollutionSocketCompositeLightweightBoundary
canonicalYMContinuumTransferToNoSpectralPollutionSocketCompositeLightweightBoundary =
  record
    { clauses = canonicalYMNoPollutionSocketClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMNoPollutionSocketBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

YMContinuumTransferToNoSpectralPollutionSocketCompositeRecordedIsTrue :
  YMContinuumTransferToNoSpectralPollutionSocketCompositeRecorded ≡ true
YMContinuumTransferToNoSpectralPollutionSocketCompositeRecordedIsTrue = refl
