module DASHI.Physics.Closure.YMContinuumBridgeCompositeLightweightBoundary where

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

rhoReference : String
rhoReference =
  "DASHI.Physics.Closure.YMContinuumUniformRhoBoundBoundary"

leakageReference : String
leakageReference =
  "DASHI.Physics.Closure.YMContinuumUniformLeakageBoundBoundary"

universalityReference : String
universalityReference =
  "DASHI.Physics.Closure.YMHyperbolicShimuraToEuclideanUniversalityBoundary"

data YMContinuumBridgeClause : Set where
  mckayRhoBudgetImported : YMContinuumBridgeClause
  exponentialLeakageBudgetImported : YMContinuumBridgeClause
  btToEuclideanGapTransferImported : YMContinuumBridgeClause
  finiteVolumeGapLowerBoundRecorded : YMContinuumBridgeClause
  continuumRGResidualHonestyRecorded : YMContinuumBridgeClause
  osWightmanAuthorityStillBlocked : YMContinuumBridgeClause

canonicalYMContinuumBridgeClauses : List YMContinuumBridgeClause
canonicalYMContinuumBridgeClauses =
  mckayRhoBudgetImported
  ∷ exponentialLeakageBudgetImported
  ∷ btToEuclideanGapTransferImported
  ∷ finiteVolumeGapLowerBoundRecorded
  ∷ continuumRGResidualHonestyRecorded
  ∷ osWightmanAuthorityStillBlocked
  ∷ []

ymContinuumBridgeClauseCount : Nat
ymContinuumBridgeClauseCount = listLength canonicalYMContinuumBridgeClauses

ymContinuumBridgeClauseCountIs6 : ymContinuumBridgeClauseCount ≡ 6
ymContinuumBridgeClauseCountIs6 = refl

data YMContinuumBridgeBlocker : Set where
  blocker-rgDimensionalTransmutationStillOpen : YMContinuumBridgeBlocker
  blocker-nospectralpollutionStillOpen : YMContinuumBridgeBlocker
  blocker-osWightmanStillOpen : YMContinuumBridgeBlocker
  blocker-continuumMassGapStillOpen : YMContinuumBridgeBlocker
  blocker-ymClayPromotionForbidden : YMContinuumBridgeBlocker

canonicalYMContinuumBridgeBlockers : List YMContinuumBridgeBlocker
canonicalYMContinuumBridgeBlockers =
  blocker-rgDimensionalTransmutationStillOpen
  ∷ blocker-nospectralpollutionStillOpen
  ∷ blocker-osWightmanStillOpen
  ∷ blocker-continuumMassGapStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMContinuumBridgeCompositeRecorded : Bool
YMContinuumBridgeCompositeRecorded = true

YMContinuumBridgeCompositeProved : Bool
YMContinuumBridgeCompositeProved = false

record YMContinuumBridgeCompositeLightweightBoundary : Set where
  field
    clauses : List YMContinuumBridgeClause
    clausesCanonical : clauses ≡ canonicalYMContinuumBridgeClauses
    blockers : List YMContinuumBridgeBlocker
    blockersCanonical : blockers ≡ canonicalYMContinuumBridgeBlockers
    clauseCountIs6 : ymContinuumBridgeClauseCount ≡ 6
    provedStillFalse : YMContinuumBridgeCompositeProved ≡ false

canonicalYMContinuumBridgeCompositeLightweightBoundary :
  YMContinuumBridgeCompositeLightweightBoundary
canonicalYMContinuumBridgeCompositeLightweightBoundary =
  record
    { clauses = canonicalYMContinuumBridgeClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMContinuumBridgeBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

YMContinuumBridgeCompositeRecordedIsTrue :
  YMContinuumBridgeCompositeRecorded ≡ true
YMContinuumBridgeCompositeRecordedIsTrue = refl
