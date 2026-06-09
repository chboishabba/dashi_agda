module DASHI.Physics.Closure.UnificationU1aHJustificationYMLaneBoundary where

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

ymU1aHText : String
ymU1aHText =
  "G_YM(A)=||dA||^2_L2 at vacuum and remains valid modulo O(A^3) for nonlinear fluctuations around A0"

data UnificationU1aHYMClause : Set where
  vacuumLinearizationEnergyRecorded : UnificationU1aHYMClause
  exactL2BilinearCrossTermRecorded : UnificationU1aHYMClause
  positivityRecorded : UnificationU1aHYMClause
  nonlinearFluctuationExpansionRecorded : UnificationU1aHYMClause
  cubicRemainderBudgetRecorded : UnificationU1aHYMClause
  spectralMassGapUseCaseRecorded : UnificationU1aHYMClause
  machineErrorBudgetRecorded : UnificationU1aHYMClause

canonicalUnificationU1aHYMClauses : List UnificationU1aHYMClause
canonicalUnificationU1aHYMClauses =
  vacuumLinearizationEnergyRecorded
  ∷ exactL2BilinearCrossTermRecorded
  ∷ positivityRecorded
  ∷ nonlinearFluctuationExpansionRecorded
  ∷ cubicRemainderBudgetRecorded
  ∷ spectralMassGapUseCaseRecorded
  ∷ machineErrorBudgetRecorded
  ∷ []

unificationU1aHYMClauseCount : Nat
unificationU1aHYMClauseCount = listLength canonicalUnificationU1aHYMClauses

unificationU1aHYMClauseCountIs7 : unificationU1aHYMClauseCount ≡ 7
unificationU1aHYMClauseCountIs7 = refl

data UnificationU1aHYMBlocker : Set where
  blocker-nonlinearGlobalAuthorityStillOpen : UnificationU1aHYMBlocker
  blocker-continuumGaugeWriteupStillOpen : UnificationU1aHYMBlocker
  blocker-unificationPromotionForbidden : UnificationU1aHYMBlocker

canonicalUnificationU1aHYMBlockers : List UnificationU1aHYMBlocker
canonicalUnificationU1aHYMBlockers =
  blocker-nonlinearGlobalAuthorityStillOpen
  ∷ blocker-continuumGaugeWriteupStillOpen
  ∷ blocker-unificationPromotionForbidden
  ∷ []

UnificationU1aHJustificationYMLaneRecorded : Bool
UnificationU1aHJustificationYMLaneRecorded = true

UnificationU1aHJustificationYMLaneProved : Bool
UnificationU1aHJustificationYMLaneProved = false

record UnificationU1aHJustificationYMLaneBoundary : Set where
  field
    clauses : List UnificationU1aHYMClause
    clausesCanonical : clauses ≡ canonicalUnificationU1aHYMClauses
    blockers : List UnificationU1aHYMBlocker
    blockersCanonical : blockers ≡ canonicalUnificationU1aHYMBlockers
    clauseCountIs7 : unificationU1aHYMClauseCount ≡ 7
    theoremStillFalse : UnificationU1aHJustificationYMLaneProved ≡ false

canonicalUnificationU1aHJustificationYMLaneBoundary :
  UnificationU1aHJustificationYMLaneBoundary
canonicalUnificationU1aHJustificationYMLaneBoundary =
  record
    { clauses = canonicalUnificationU1aHYMClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUnificationU1aHYMBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    }

UnificationU1aHJustificationYMLaneRecordedIsTrue :
  UnificationU1aHJustificationYMLaneRecorded ≡ true
UnificationU1aHJustificationYMLaneRecordedIsTrue = refl
