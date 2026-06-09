module DASHI.Physics.Closure.YMKillingBoundarySpectralGapExplicitBoundary where

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

spectralGapFormulaText : String
spectralGapFormulaText =
  "gamma_d >= Casimir_min(G)/4 > 0"

data YMSpectralGapExplicitClause : Set where
  finiteSelfAdjointQuotientHamiltonianConsumed : YMSpectralGapExplicitClause
  finitePSDRecorded : YMSpectralGapExplicitClause
  lambdaMinZeroRecorded : YMSpectralGapExplicitClause
  smallestPositiveEigenvalueRecorded : YMSpectralGapExplicitClause
  explicitCasimirQuarterLowerBoundRecorded : YMSpectralGapExplicitClause
  numericalSmokeConstantRecorded : YMSpectralGapExplicitClause
  continuumGapRouteFedOnlyThroughLaterConsumers : YMSpectralGapExplicitClause

canonicalYMSpectralGapExplicitClauses : List YMSpectralGapExplicitClause
canonicalYMSpectralGapExplicitClauses =
  finiteSelfAdjointQuotientHamiltonianConsumed
  ∷ finitePSDRecorded
  ∷ lambdaMinZeroRecorded
  ∷ smallestPositiveEigenvalueRecorded
  ∷ explicitCasimirQuarterLowerBoundRecorded
  ∷ numericalSmokeConstantRecorded
  ∷ continuumGapRouteFedOnlyThroughLaterConsumers
  ∷ []

ymSpectralGapExplicitClauseCount : Nat
ymSpectralGapExplicitClauseCount = listLength canonicalYMSpectralGapExplicitClauses

ymSpectralGapExplicitClauseCountIs7 : ymSpectralGapExplicitClauseCount ≡ 7
ymSpectralGapExplicitClauseCountIs7 = refl

data YMSpectralGapExplicitBlocker : Set where
  blocker-selfAdjointHamiltonianTheoremOpen : YMSpectralGapExplicitBlocker
  blocker-explicitCasimirEstimateProofOpen : YMSpectralGapExplicitBlocker
  blocker-finiteGapToContinuumTransferOpen : YMSpectralGapExplicitBlocker
  blocker-ymClayPromotionForbidden : YMSpectralGapExplicitBlocker

canonicalYMSpectralGapExplicitBlockers : List YMSpectralGapExplicitBlocker
canonicalYMSpectralGapExplicitBlockers =
  blocker-selfAdjointHamiltonianTheoremOpen
  ∷ blocker-explicitCasimirEstimateProofOpen
  ∷ blocker-finiteGapToContinuumTransferOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMKillingBoundarySpectralGapExplicitRecorded : Bool
YMKillingBoundarySpectralGapExplicitRecorded = true

YMKillingBoundarySpectralGapExplicitProved : Bool
YMKillingBoundarySpectralGapExplicitProved = false

record YMKillingBoundarySpectralGapExplicitBoundary : Set where
  field
    clauses : List YMSpectralGapExplicitClause
    clausesCanonical : clauses ≡ canonicalYMSpectralGapExplicitClauses
    blockers : List YMSpectralGapExplicitBlocker
    blockersCanonical : blockers ≡ canonicalYMSpectralGapExplicitBlockers
    clauseCountIs7 : ymSpectralGapExplicitClauseCount ≡ 7
    theoremStillFalse :
      YMKillingBoundarySpectralGapExplicitProved ≡ false

canonicalYMKillingBoundarySpectralGapExplicitBoundary :
  YMKillingBoundarySpectralGapExplicitBoundary
canonicalYMKillingBoundarySpectralGapExplicitBoundary =
  record
    { clauses = canonicalYMSpectralGapExplicitClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMSpectralGapExplicitBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    }

YMKillingBoundarySpectralGapExplicitRecordedIsTrue :
  YMKillingBoundarySpectralGapExplicitRecorded ≡ true
YMKillingBoundarySpectralGapExplicitRecordedIsTrue = refl
