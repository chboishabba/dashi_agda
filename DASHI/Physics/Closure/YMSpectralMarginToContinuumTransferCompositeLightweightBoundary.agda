module DASHI.Physics.Closure.YMSpectralMarginToContinuumTransferCompositeLightweightBoundary where

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

data YMSpectralContinuumClause : Set where
  spectralMarginRouteImported : YMSpectralContinuumClause
  continuumBridgeImported : YMSpectralContinuumClause
  finiteVolumeToBulkGapRecorded : YMSpectralContinuumClause
  rgResidualHonestyRetained : YMSpectralContinuumClause
  noSpectralPollutionSocketRecorded : YMSpectralContinuumClause
  osWightmanSocketRecorded : YMSpectralContinuumClause

canonicalYMSpectralContinuumClauses : List YMSpectralContinuumClause
canonicalYMSpectralContinuumClauses =
  spectralMarginRouteImported
  ∷ continuumBridgeImported
  ∷ finiteVolumeToBulkGapRecorded
  ∷ rgResidualHonestyRetained
  ∷ noSpectralPollutionSocketRecorded
  ∷ osWightmanSocketRecorded
  ∷ []

ymSpectralContinuumClauseCount : Nat
ymSpectralContinuumClauseCount = listLength canonicalYMSpectralContinuumClauses

ymSpectralContinuumClauseCountIs6 : ymSpectralContinuumClauseCount ≡ 6
ymSpectralContinuumClauseCountIs6 = refl

data YMSpectralContinuumBlocker : Set where
  blocker-continuumTransferStillOpen : YMSpectralContinuumBlocker
  blocker-nospectralpollutionStillOpen : YMSpectralContinuumBlocker
  blocker-osWightmanStillOpen : YMSpectralContinuumBlocker
  blocker-ymClayPromotionForbidden : YMSpectralContinuumBlocker

canonicalYMSpectralContinuumBlockers : List YMSpectralContinuumBlocker
canonicalYMSpectralContinuumBlockers =
  blocker-continuumTransferStillOpen
  ∷ blocker-nospectralpollutionStillOpen
  ∷ blocker-osWightmanStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMSpectralMarginToContinuumTransferCompositeRecorded : Bool
YMSpectralMarginToContinuumTransferCompositeRecorded = true

YMSpectralMarginToContinuumTransferCompositeProved : Bool
YMSpectralMarginToContinuumTransferCompositeProved = false

record YMSpectralMarginToContinuumTransferCompositeLightweightBoundary : Set where
  field
    clauses : List YMSpectralContinuumClause
    clausesCanonical : clauses ≡ canonicalYMSpectralContinuumClauses
    blockers : List YMSpectralContinuumBlocker
    blockersCanonical : blockers ≡ canonicalYMSpectralContinuumBlockers
    clauseCountIs6 : ymSpectralContinuumClauseCount ≡ 6
    provedStillFalse :
      YMSpectralMarginToContinuumTransferCompositeProved ≡ false

canonicalYMSpectralMarginToContinuumTransferCompositeLightweightBoundary :
  YMSpectralMarginToContinuumTransferCompositeLightweightBoundary
canonicalYMSpectralMarginToContinuumTransferCompositeLightweightBoundary =
  record
    { clauses = canonicalYMSpectralContinuumClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMSpectralContinuumBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

YMSpectralMarginToContinuumTransferCompositeRecordedIsTrue :
  YMSpectralMarginToContinuumTransferCompositeRecorded ≡ true
YMSpectralMarginToContinuumTransferCompositeRecordedIsTrue = refl
