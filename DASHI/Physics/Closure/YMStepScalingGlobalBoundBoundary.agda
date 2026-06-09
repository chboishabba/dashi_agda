module DASHI.Physics.Closure.YMStepScalingGlobalBoundBoundary where

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

stepScalingFormulaText : String
stepScalingFormulaText =
  "sigma_d(u) <= (1+((p+1)*C_G/gamma_low)*g0^2)*u"

productBoundText : String
productBoundText =
  "sigma^(n)(u) <= u*exp(C_sigma') with n*g0^2 -> 1/b1"

data YMStepScalingClause : Set where
  finiteGapLowerBoundConsumed : YMStepScalingClause
  rhoUpperEnvelopeConsumed : YMStepScalingClause
  oneLayerWeylPerturbationBudgetRecorded : YMStepScalingClause
  stepScalingFunctionDefined : YMStepScalingClause
  singleStepUpperBoundRecorded : YMStepScalingClause
  runningCouplingCompensatesProductGrowth : YMStepScalingClause
  globalExponentialBoundRecorded : YMStepScalingClause

canonicalYMStepScalingClauses : List YMStepScalingClause
canonicalYMStepScalingClauses =
  finiteGapLowerBoundConsumed
  ∷ rhoUpperEnvelopeConsumed
  ∷ oneLayerWeylPerturbationBudgetRecorded
  ∷ stepScalingFunctionDefined
  ∷ singleStepUpperBoundRecorded
  ∷ runningCouplingCompensatesProductGrowth
  ∷ globalExponentialBoundRecorded
  ∷ []

ymStepScalingClauseCount : Nat
ymStepScalingClauseCount = listLength canonicalYMStepScalingClauses

ymStepScalingClauseCountIs7 : ymStepScalingClauseCount ≡ 7
ymStepScalingClauseCountIs7 = refl

data YMStepScalingBlocker : Set where
  blocker-runningCouplingProofOpen : YMStepScalingBlocker
  blocker-weylMonotonicityBudgetProofOpen : YMStepScalingBlocker
  blocker-reflectionPositivityStillOpen : YMStepScalingBlocker
  blocker-finalMassGapAssemblyStillOpen : YMStepScalingBlocker
  blocker-ymClayPromotionForbidden : YMStepScalingBlocker

canonicalYMStepScalingBlockers : List YMStepScalingBlocker
canonicalYMStepScalingBlockers =
  blocker-runningCouplingProofOpen
  ∷ blocker-weylMonotonicityBudgetProofOpen
  ∷ blocker-reflectionPositivityStillOpen
  ∷ blocker-finalMassGapAssemblyStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMStepScalingGlobalBoundRecorded : Bool
YMStepScalingGlobalBoundRecorded = true

YMStepScalingGlobalBoundProved : Bool
YMStepScalingGlobalBoundProved = false

record YMStepScalingGlobalBoundBoundary : Set where
  field
    clauses : List YMStepScalingClause
    clausesCanonical : clauses ≡ canonicalYMStepScalingClauses
    blockers : List YMStepScalingBlocker
    blockersCanonical : blockers ≡ canonicalYMStepScalingBlockers
    clauseCountIs7 : ymStepScalingClauseCount ≡ 7
    theoremStillFalse : YMStepScalingGlobalBoundProved ≡ false

canonicalYMStepScalingGlobalBoundBoundary :
  YMStepScalingGlobalBoundBoundary
canonicalYMStepScalingGlobalBoundBoundary =
  record
    { clauses = canonicalYMStepScalingClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMStepScalingBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    }

YMStepScalingGlobalBoundRecordedIsTrue :
  YMStepScalingGlobalBoundRecorded ≡ true
YMStepScalingGlobalBoundRecordedIsTrue = refl
