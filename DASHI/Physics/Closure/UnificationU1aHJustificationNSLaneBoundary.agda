module DASHI.Physics.Closure.UnificationU1aHJustificationNSLaneBoundary where

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

nsU1aHText : String
nsU1aHText =
  "G_NS(s)=||s||^2_H10 = integral_Br |grad s|^2 dx, so G_NS(s1+s2)-G_NS(s1)-G_NS(s2)=2< s1 , s2 >_H1"

data UnificationU1aHNSClause : Set where
  h10EnergyFunctionalRecorded : UnificationU1aHNSClause
  symmetricBilinearCrossTermRecorded : UnificationU1aHNSClause
  positivityRecorded : UnificationU1aHNSClause
  nullClassTrivialUnderH10Recorded : UnificationU1aHNSClause
  quotientNotNeededRecorded : UnificationU1aHNSClause
  machineErrorBudgetRecorded : UnificationU1aHNSClause

canonicalUnificationU1aHNSClauses : List UnificationU1aHNSClause
canonicalUnificationU1aHNSClauses =
  h10EnergyFunctionalRecorded
  ∷ symmetricBilinearCrossTermRecorded
  ∷ positivityRecorded
  ∷ nullClassTrivialUnderH10Recorded
  ∷ quotientNotNeededRecorded
  ∷ machineErrorBudgetRecorded
  ∷ []

unificationU1aHNSClauseCount : Nat
unificationU1aHNSClauseCount = listLength canonicalUnificationU1aHNSClauses

unificationU1aHNSClauseCountIs6 : unificationU1aHNSClauseCount ≡ 6
unificationU1aHNSClauseCountIs6 = refl

data UnificationU1aHNSBlocker : Set where
  blocker-functionalAnalyticWriteupStillOpen : UnificationU1aHNSBlocker
  blocker-pdeLaneTranslationStillOpen : UnificationU1aHNSBlocker
  blocker-unificationPromotionForbidden : UnificationU1aHNSBlocker

canonicalUnificationU1aHNSBlockers : List UnificationU1aHNSBlocker
canonicalUnificationU1aHNSBlockers =
  blocker-functionalAnalyticWriteupStillOpen
  ∷ blocker-pdeLaneTranslationStillOpen
  ∷ blocker-unificationPromotionForbidden
  ∷ []

UnificationU1aHJustificationNSLaneRecorded : Bool
UnificationU1aHJustificationNSLaneRecorded = true

UnificationU1aHJustificationNSLaneProved : Bool
UnificationU1aHJustificationNSLaneProved = false

record UnificationU1aHJustificationNSLaneBoundary : Set where
  field
    clauses : List UnificationU1aHNSClause
    clausesCanonical : clauses ≡ canonicalUnificationU1aHNSClauses
    blockers : List UnificationU1aHNSBlocker
    blockersCanonical : blockers ≡ canonicalUnificationU1aHNSBlockers
    clauseCountIs6 : unificationU1aHNSClauseCount ≡ 6
    theoremStillFalse : UnificationU1aHJustificationNSLaneProved ≡ false

canonicalUnificationU1aHJustificationNSLaneBoundary :
  UnificationU1aHJustificationNSLaneBoundary
canonicalUnificationU1aHJustificationNSLaneBoundary =
  record
    { clauses = canonicalUnificationU1aHNSClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUnificationU1aHNSBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; theoremStillFalse = refl
    }

UnificationU1aHJustificationNSLaneRecordedIsTrue :
  UnificationU1aHJustificationNSLaneRecorded ≡ true
UnificationU1aHJustificationNSLaneRecordedIsTrue = refl
