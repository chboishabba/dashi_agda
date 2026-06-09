module DASHI.Physics.Closure.YMContinuumUniformLeakageBoundBoundary where

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

leakageFormulaText : String
leakageFormulaText =
  "L_d <= C_G * p^(-d)"

data YMContinuumLeakageClause : Set where
  nearVacuumModeSequenceRecorded : YMContinuumLeakageClause
  holonomyFloorRecorded : YMContinuumLeakageClause
  boundarySurfaceVolumeDecayRecorded : YMContinuumLeakageClause
  exponentialLeakageDecayRecorded : YMContinuumLeakageClause
  continuumLeakageVanishingTargetRecorded : YMContinuumLeakageClause

canonicalYMContinuumLeakageClauses : List YMContinuumLeakageClause
canonicalYMContinuumLeakageClauses =
  nearVacuumModeSequenceRecorded
  ∷ holonomyFloorRecorded
  ∷ boundarySurfaceVolumeDecayRecorded
  ∷ exponentialLeakageDecayRecorded
  ∷ continuumLeakageVanishingTargetRecorded
  ∷ []

ymContinuumLeakageClauseCount : Nat
ymContinuumLeakageClauseCount = listLength canonicalYMContinuumLeakageClauses

ymContinuumLeakageClauseCountIs5 : ymContinuumLeakageClauseCount ≡ 5
ymContinuumLeakageClauseCountIs5 = refl

data YMContinuumLeakageBlocker : Set where
  blocker-holonomyLowerBoundStillOpen : YMContinuumLeakageBlocker
  blocker-boundaryConventionDependenceStillOpen : YMContinuumLeakageBlocker
  blocker-continuumLeakageProofStillOpen : YMContinuumLeakageBlocker
  blocker-ymClayPromotionForbidden : YMContinuumLeakageBlocker

canonicalYMContinuumLeakageBlockers : List YMContinuumLeakageBlocker
canonicalYMContinuumLeakageBlockers =
  blocker-holonomyLowerBoundStillOpen
  ∷ blocker-boundaryConventionDependenceStillOpen
  ∷ blocker-continuumLeakageProofStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMContinuumUniformLeakageBoundRecorded : Bool
YMContinuumUniformLeakageBoundRecorded = true

YMContinuumUniformLeakageBoundProved : Bool
YMContinuumUniformLeakageBoundProved = false

record YMContinuumUniformLeakageBoundBoundary : Set where
  field
    clauses : List YMContinuumLeakageClause
    clausesCanonical : clauses ≡ canonicalYMContinuumLeakageClauses
    blockers : List YMContinuumLeakageBlocker
    blockersCanonical : blockers ≡ canonicalYMContinuumLeakageBlockers
    clauseCountIs5 : ymContinuumLeakageClauseCount ≡ 5
    leakageBoundStillFalse : YMContinuumUniformLeakageBoundProved ≡ false

canonicalYMContinuumUniformLeakageBoundBoundary :
  YMContinuumUniformLeakageBoundBoundary
canonicalYMContinuumUniformLeakageBoundBoundary =
  record
    { clauses = canonicalYMContinuumLeakageClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMContinuumLeakageBlockers
    ; blockersCanonical = refl
    ; clauseCountIs5 = refl
    ; leakageBoundStillFalse = refl
    }

YMContinuumUniformLeakageBoundRecordedIsTrue :
  YMContinuumUniformLeakageBoundRecorded ≡ true
YMContinuumUniformLeakageBoundRecordedIsTrue = refl
