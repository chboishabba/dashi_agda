module DASHI.Physics.Closure.YMContinuumUniformRhoBoundBoundary where

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

mckayDensityText : String
mckayDensityText =
  "rho_tree(E)=((p+1)*sqrt(4p-E^2))/(2*pi*(p+1-E^2/4))"

mckaySupText : String
mckaySupText =
  "||rho_tree||_L∞=(p+1)/pi"

data YMContinuumRhoClause : Set where
  mckayWeakLimitRecorded : YMContinuumRhoClause
  p2CaseRecorded : YMContinuumRhoClause
  p3CaseRecorded : YMContinuumRhoClause
  p5CaseRecorded : YMContinuumRhoClause
  p7CaseRecorded : YMContinuumRhoClause
  casimirShiftBudgetRecorded : YMContinuumRhoClause
  continuumUniformRhoTargetRecorded : YMContinuumRhoClause

canonicalYMContinuumRhoClauses : List YMContinuumRhoClause
canonicalYMContinuumRhoClauses =
  mckayWeakLimitRecorded
  ∷ p2CaseRecorded
  ∷ p3CaseRecorded
  ∷ p5CaseRecorded
  ∷ p7CaseRecorded
  ∷ casimirShiftBudgetRecorded
  ∷ continuumUniformRhoTargetRecorded
  ∷ []

ymContinuumRhoClauseCount : Nat
ymContinuumRhoClauseCount = listLength canonicalYMContinuumRhoClauses

ymContinuumRhoClauseCountIs7 : ymContinuumRhoClauseCount ≡ 7
ymContinuumRhoClauseCountIs7 = refl

data YMContinuumRhoBlocker : Set where
  blocker-mckayToHamiltonianTransferOpen : YMContinuumRhoBlocker
  blocker-lieAlgebraShiftControlOpen : YMContinuumRhoBlocker
  blocker-hamiltonianDominationStillOpen : YMContinuumRhoBlocker
  blocker-continuumMassGapStillOpen : YMContinuumRhoBlocker

canonicalYMContinuumRhoBlockers : List YMContinuumRhoBlocker
canonicalYMContinuumRhoBlockers =
  blocker-mckayToHamiltonianTransferOpen
  ∷ blocker-lieAlgebraShiftControlOpen
  ∷ blocker-hamiltonianDominationStillOpen
  ∷ blocker-continuumMassGapStillOpen
  ∷ []

YMContinuumUniformRhoBoundRecorded : Bool
YMContinuumUniformRhoBoundRecorded = true

YMContinuumUniformRhoBoundProved : Bool
YMContinuumUniformRhoBoundProved = false

YMClayPromotedFromRhoBound : Bool
YMClayPromotedFromRhoBound = false

record YMContinuumUniformRhoBoundBoundary : Set where
  field
    clauses : List YMContinuumRhoClause
    clausesCanonical : clauses ≡ canonicalYMContinuumRhoClauses
    blockers : List YMContinuumRhoBlocker
    blockersCanonical : blockers ≡ canonicalYMContinuumRhoBlockers
    clauseCountIs7 : ymContinuumRhoClauseCount ≡ 7
    rhoBoundStillFalse : YMContinuumUniformRhoBoundProved ≡ false
    ymClayStillFalse : YMClayPromotedFromRhoBound ≡ false

canonicalYMContinuumUniformRhoBoundBoundary :
  YMContinuumUniformRhoBoundBoundary
canonicalYMContinuumUniformRhoBoundBoundary =
  record
    { clauses = canonicalYMContinuumRhoClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMContinuumRhoBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; rhoBoundStillFalse = refl
    ; ymClayStillFalse = refl
    }

YMContinuumUniformRhoBoundRecordedIsTrue :
  YMContinuumUniformRhoBoundRecorded ≡ true
YMContinuumUniformRhoBoundRecordedIsTrue = refl
