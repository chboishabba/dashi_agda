module DASHI.Physics.Closure.YMKillingBoundaryFluxCancellationLightweightBoundary where

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

oppositeFaceReference : String
oppositeFaceReference =
  "DASHI.Physics.Closure.YMKillingBoundaryOppositeFaceInvolutionLightweightBoundary"

orientationReference : String
orientationReference =
  "DASHI.Physics.Closure.YMKillingBoundaryOrientationCancellationBoundary"

gaugeDomainReference : String
gaugeDomainReference =
  "DASHI.Physics.Closure.YMKillingBoundaryGaugeDomainPreservationBoundary"

data FluxCancellationClause : Set where
  pairBoundaryFacesByOppositeMap :
    FluxCancellationClause
  matchPairedBoundaryWeights :
    FluxCancellationClause
  cancelOppositeOrientationSigns :
    FluxCancellationClause
  identifyPairedFluxIntegrands :
    FluxCancellationClause
  sumPairedBoundaryFluxToZero :
    FluxCancellationClause
  preserveGaugeBoundaryCompatibility :
    FluxCancellationClause
  absorbBoundaryContributionIntoSymmetricForm :
    FluxCancellationClause
  feedFiniteSelfAdjointnessRoute :
    FluxCancellationClause

canonicalFluxCancellationClauses : List FluxCancellationClause
canonicalFluxCancellationClauses =
  pairBoundaryFacesByOppositeMap
  ∷ matchPairedBoundaryWeights
  ∷ cancelOppositeOrientationSigns
  ∷ identifyPairedFluxIntegrands
  ∷ sumPairedBoundaryFluxToZero
  ∷ preserveGaugeBoundaryCompatibility
  ∷ absorbBoundaryContributionIntoSymmetricForm
  ∷ feedFiniteSelfAdjointnessRoute
  ∷ []

fluxCancellationClauseCount : Nat
fluxCancellationClauseCount = listLength canonicalFluxCancellationClauses

fluxCancellationClauseCountIs8 : fluxCancellationClauseCount ≡ 8
fluxCancellationClauseCountIs8 = refl

data FluxCancellationBudget : Set where
  oppositeFaceResidualBudget :
    FluxCancellationBudget
  weightMismatchBudget :
    FluxCancellationBudget
  orientationMismatchBudget :
    FluxCancellationBudget
  gaugeBoundaryLeakBudget :
    FluxCancellationBudget

canonicalFluxCancellationBudgets : List FluxCancellationBudget
canonicalFluxCancellationBudgets =
  oppositeFaceResidualBudget
  ∷ weightMismatchBudget
  ∷ orientationMismatchBudget
  ∷ gaugeBoundaryLeakBudget
  ∷ []

fluxCancellationBudgetCount : Nat
fluxCancellationBudgetCount = listLength canonicalFluxCancellationBudgets

fluxCancellationBudgetCountIs4 : fluxCancellationBudgetCount ≡ 4
fluxCancellationBudgetCountIs4 = refl

data FluxCancellationBlocker : Set where
  blocker-flux-cancellation-theorem-unproved :
    FluxCancellationBlocker
  blocker-self-adjoint-boundary-form-open :
    FluxCancellationBlocker
  blocker-ym1-open :
    FluxCancellationBlocker
  blocker-ym-clay-forbidden :
    FluxCancellationBlocker

canonicalFluxCancellationBlockers : List FluxCancellationBlocker
canonicalFluxCancellationBlockers =
  blocker-flux-cancellation-theorem-unproved
  ∷ blocker-self-adjoint-boundary-form-open
  ∷ blocker-ym1-open
  ∷ blocker-ym-clay-forbidden
  ∷ []

fluxCancellationBlockerCount : Nat
fluxCancellationBlockerCount = listLength canonicalFluxCancellationBlockers

fluxCancellationBlockerCountIs4 : fluxCancellationBlockerCount ≡ 4
fluxCancellationBlockerCountIs4 = refl

FluxCancellationTheoremProvedLightweight : Bool
FluxCancellationTheoremProvedLightweight = false

FluxCancellationTheoremProvedLightweightIsFalse :
  FluxCancellationTheoremProvedLightweight ≡ false
FluxCancellationTheoremProvedLightweightIsFalse = refl

record YMKillingBoundaryFluxCancellationLightweightBoundary : Set where
  field
    clauses : List FluxCancellationClause
    clausesAreCanonical : clauses ≡ canonicalFluxCancellationClauses
    budgets : List FluxCancellationBudget
    budgetsAreCanonical : budgets ≡ canonicalFluxCancellationBudgets
    blockers : List FluxCancellationBlocker
    blockersAreCanonical : blockers ≡ canonicalFluxCancellationBlockers
    clauseCountIs8 : fluxCancellationClauseCount ≡ 8
    budgetCountIs4 : fluxCancellationBudgetCount ≡ 4
    blockerCountIs4 : fluxCancellationBlockerCount ≡ 4
    theoremStillFalse : FluxCancellationTheoremProvedLightweight ≡ false

canonicalYMKillingBoundaryFluxCancellationLightweightBoundary :
  YMKillingBoundaryFluxCancellationLightweightBoundary
canonicalYMKillingBoundaryFluxCancellationLightweightBoundary =
  record
    { clauses = canonicalFluxCancellationClauses
    ; clausesAreCanonical = refl
    ; budgets = canonicalFluxCancellationBudgets
    ; budgetsAreCanonical = refl
    ; blockers = canonicalFluxCancellationBlockers
    ; blockersAreCanonical = refl
    ; clauseCountIs8 = refl
    ; budgetCountIs4 = refl
    ; blockerCountIs4 = refl
    ; theoremStillFalse = refl
    }

YMFluxCancellationLightweightBoundaryRecorded : Bool
YMFluxCancellationLightweightBoundaryRecorded = true

YMFluxCancellationLightweightBoundaryRecordedIsTrue :
  YMFluxCancellationLightweightBoundaryRecorded ≡ true
YMFluxCancellationLightweightBoundaryRecordedIsTrue = refl
