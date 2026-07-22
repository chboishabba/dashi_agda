{-# OPTIONS --safe #-}
module DASHI.Cognition.KepplerAdmissibility where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Control.DynamicalTernarySignal
  using (compareNat)

------------------------------------------------------------------------
-- Keppler has three formally distinct roles.
--
-- descriptive : read a signal without changing state or boundary
-- parametric  : move the admissibility boundary while preserving state
-- causal      : update the state before classifying it
--
-- Keeping separate result types prevents these meanings from being silently
-- conflated.

record DescriptiveObservation : Set where
  constructor descriptive-observation
  field
    observedState : Nat
    descriptiveSignal : Trit

open DescriptiveObservation public

describeKeppler : Nat → Nat → DescriptiveObservation
describeKeppler state control =
  descriptive-observation state (compareNat state control)

descriptive-state-preserved :
  (state control : Nat) →
  observedState (describeKeppler state control) ≡ state
descriptive-state-preserved state control = refl

record ParametricSnapshot : Set where
  constructor parametric-snapshot
  field
    parametricState : Nat
    shiftedBoundary : Nat
    parametricSignal : Trit

open ParametricSnapshot public

parameteriseKeppler :
  Nat →
  Nat →
  Nat →
  ParametricSnapshot
parameteriseKeppler baseBoundary control state =
  parametric-snapshot
    state
    (baseBoundary + control)
    (compareNat state (baseBoundary + control))

parametric-state-preserved :
  (baseBoundary control state : Nat) →
  parametricState
    (parameteriseKeppler baseBoundary control state)
    ≡ state
parametric-state-preserved baseBoundary control state = refl

parametric-boundary-shifts :
  (baseBoundary control state : Nat) →
  shiftedBoundary
    (parameteriseKeppler baseBoundary control state)
    ≡ baseBoundary + control
parametric-boundary-shifts baseBoundary control state = refl

record CausalSnapshot : Set where
  constructor causal-snapshot
  field
    stateBefore : Nat
    stateAfter : Nat
    causalBoundary : Nat
    causalSignal : Trit

open CausalSnapshot public

causalUpdate : Nat → Nat → Nat
causalUpdate control state =
  state ∸ control

causeKeppler :
  Nat →
  Nat →
  Nat →
  CausalSnapshot
causeKeppler boundary control state =
  causal-snapshot
    state
    (causalUpdate control state)
    boundary
    (compareNat (causalUpdate control state) boundary)

causal-state-evolves :
  (boundary control state : Nat) →
  stateAfter (causeKeppler boundary control state)
  ≡ causalUpdate control state
causal-state-evolves boundary control state = refl

------------------------------------------------------------------------
-- Concrete separation witnesses.

descriptive-example-state :
  observedState (describeKeppler 3 2) ≡ 3
descriptive-example-state = refl

parametric-example-crosses-boundary :
  parametricSignal (parameteriseKeppler 2 2 3) ≡ neg
parametric-example-crosses-boundary = refl

causal-example-crosses-boundary :
  causalSignal (causeKeppler 2 2 3) ≡ neg
causal-example-crosses-boundary = refl

unperturbed-example-is-admissible :
  compareNat 3 2 ≡ pos
unperturbed-example-is-admissible = refl

record KepplerAdmissibilityReceipt : Set where
  constructor keppler-admissibility-receipt
  field
    descriptiveRoleSeparated : Bool
    parametricRoleSeparated : Bool
    causalRoleSeparated : Bool
    quantumSubstrateRequired : Bool
    quantumSubstrateRequiredIsFalse :
      quantumSubstrateRequired ≡ false

kepplerAdmissibilityReceipt : KepplerAdmissibilityReceipt
kepplerAdmissibilityReceipt =
  keppler-admissibility-receipt
    true true true
    false refl
