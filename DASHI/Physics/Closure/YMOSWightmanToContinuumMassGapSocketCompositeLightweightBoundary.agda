module DASHI.Physics.Closure.YMOSWightmanToContinuumMassGapSocketCompositeLightweightBoundary where

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

data YMOSWightmanMassGapClause : Set where
  osWightmanSocketImported : YMOSWightmanMassGapClause
  rgInvariantScaleInputRecorded : YMOSWightmanMassGapClause
  finiteGapInputRecorded : YMOSWightmanMassGapClause
  finalMassGapAssemblySocketRecorded : YMOSWightmanMassGapClause
  clayPromotionStillBlocked : YMOSWightmanMassGapClause

canonicalYMOSWightmanMassGapClauses : List YMOSWightmanMassGapClause
canonicalYMOSWightmanMassGapClauses =
  osWightmanSocketImported
  ∷ rgInvariantScaleInputRecorded
  ∷ finiteGapInputRecorded
  ∷ finalMassGapAssemblySocketRecorded
  ∷ clayPromotionStillBlocked
  ∷ []

ymOSWightmanMassGapClauseCount : Nat
ymOSWightmanMassGapClauseCount = listLength canonicalYMOSWightmanMassGapClauses

ymOSWightmanMassGapClauseCountIs5 : ymOSWightmanMassGapClauseCount ≡ 5
ymOSWightmanMassGapClauseCountIs5 = refl

data YMOSWightmanMassGapBlocker : Set where
  blocker-osWightmanAuthorityStillOpen : YMOSWightmanMassGapBlocker
  blocker-rgInvariantScaleAssemblyStillOpen : YMOSWightmanMassGapBlocker
  blocker-finalMassGapAssemblyStillOpen : YMOSWightmanMassGapBlocker
  blocker-ymClayPromotionForbidden : YMOSWightmanMassGapBlocker

canonicalYMOSWightmanMassGapBlockers : List YMOSWightmanMassGapBlocker
canonicalYMOSWightmanMassGapBlockers =
  blocker-osWightmanAuthorityStillOpen
  ∷ blocker-rgInvariantScaleAssemblyStillOpen
  ∷ blocker-finalMassGapAssemblyStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMOSWightmanToContinuumMassGapSocketCompositeRecorded : Bool
YMOSWightmanToContinuumMassGapSocketCompositeRecorded = true

YMOSWightmanToContinuumMassGapSocketCompositeProved : Bool
YMOSWightmanToContinuumMassGapSocketCompositeProved = false

record YMOSWightmanToContinuumMassGapSocketCompositeLightweightBoundary : Set where
  field
    clauses : List YMOSWightmanMassGapClause
    clausesCanonical : clauses ≡ canonicalYMOSWightmanMassGapClauses
    blockers : List YMOSWightmanMassGapBlocker
    blockersCanonical : blockers ≡ canonicalYMOSWightmanMassGapBlockers
    clauseCountIs5 : ymOSWightmanMassGapClauseCount ≡ 5
    provedStillFalse :
      YMOSWightmanToContinuumMassGapSocketCompositeProved ≡ false

canonicalYMOSWightmanToContinuumMassGapSocketCompositeLightweightBoundary :
  YMOSWightmanToContinuumMassGapSocketCompositeLightweightBoundary
canonicalYMOSWightmanToContinuumMassGapSocketCompositeLightweightBoundary =
  record
    { clauses = canonicalYMOSWightmanMassGapClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMOSWightmanMassGapBlockers
    ; blockersCanonical = refl
    ; clauseCountIs5 = refl
    ; provedStillFalse = refl
    }

YMOSWightmanToContinuumMassGapSocketCompositeRecordedIsTrue :
  YMOSWightmanToContinuumMassGapSocketCompositeRecorded ≡ true
YMOSWightmanToContinuumMassGapSocketCompositeRecordedIsTrue = refl
