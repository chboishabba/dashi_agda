module DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; _*_; _+_; _≤_; z≤n; s≤s)

------------------------------------------------------------------------
-- Transition primitive-estimate surface.
--
-- The transition profile is the next live Stage 3 lane after adversarial.
-- The intended closure pattern is exponent-parametric:
--
--   row    <= A_trans / N^alpha
--   column <= B_trans / N^beta
--   alpha + beta >= 2
--
-- so the weighted product closes at least at the Stage 3 threshold N^-2.

data TransitionClass : Set where
  thinTransition : TransitionClass
  balancedTransition : TransitionClass
  rowThickTransition : TransitionClass
  columnThickTransition : TransitionClass

------------------------------------------------------------------------
-- Transition exponent table.
--
-- These formulas make the intended count / magnitude bookkeeping explicit
-- before the concrete incidence theorems exist.

transitionRowCountExp : TransitionClass -> ℕ
transitionRowCountExp thinTransition = 0
transitionRowCountExp balancedTransition = 1
transitionRowCountExp rowThickTransition = 2
transitionRowCountExp columnThickTransition = 1

transitionColumnCountExp : TransitionClass -> ℕ
transitionColumnCountExp thinTransition = 1
transitionColumnCountExp balancedTransition = 1
transitionColumnCountExp rowThickTransition = 1
transitionColumnCountExp columnThickTransition = 2

transitionMagnitudeExp : TransitionClass -> ℕ
transitionMagnitudeExp thinTransition = 2
transitionMagnitudeExp balancedTransition = 2
transitionMagnitudeExp rowThickTransition = 3
transitionMagnitudeExp columnThickTransition = 3

-- The decay exponents are written explicitly so the class table stays
-- theorem-facing even before the concrete arithmetic route is discharged.

transitionRowDecayExp : TransitionClass -> ℕ
transitionRowDecayExp thinTransition = 2
transitionRowDecayExp balancedTransition = 1
transitionRowDecayExp rowThickTransition = 1
transitionRowDecayExp columnThickTransition = 2

transitionColumnDecayExp : TransitionClass -> ℕ
transitionColumnDecayExp thinTransition = 1
transitionColumnDecayExp balancedTransition = 1
transitionColumnDecayExp rowThickTransition = 2
transitionColumnDecayExp columnThickTransition = 1

transitionClassExponentSumAtLeastTwo :
  (c : TransitionClass) ->
  2 ≤ transitionRowDecayExp c + transitionColumnDecayExp c
transitionClassExponentSumAtLeastTwo thinTransition =
  s≤s (s≤s z≤n)
transitionClassExponentSumAtLeastTwo balancedTransition =
  s≤s (s≤s z≤n)
transitionClassExponentSumAtLeastTwo rowThickTransition =
  s≤s (s≤s z≤n)
transitionClassExponentSumAtLeastTwo columnThickTransition =
  s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- Formula-level count envelopes.

transitionRowCountBound : TransitionClass -> ℕ -> ℕ
transitionRowCountBound thinTransition _ = 1
transitionRowCountBound balancedTransition N = N
transitionRowCountBound rowThickTransition N = N * N
transitionRowCountBound columnThickTransition N = N

transitionColumnCountBound : TransitionClass -> ℕ -> ℕ
transitionColumnCountBound thinTransition N = N
transitionColumnCountBound balancedTransition N = N
transitionColumnCountBound rowThickTransition N = N
transitionColumnCountBound columnThickTransition N = N * N

------------------------------------------------------------------------
-- Primitive theorem obligations.
--
-- These are the actual next mathematical slots. They remain uninhabited here.

postulate
  TransitionIncidence : Set

  transitionClassification :
    TransitionIncidence -> TransitionClass

  transitionIncidenceClassified :
    (N : ℕ) -> Set

  transitionRowCountBoundObligated :
    (N : ℕ) -> (c : TransitionClass) -> Set

  transitionColumnCountBoundObligated :
    (N : ℕ) -> (c : TransitionClass) -> Set

  transitionPiProductScaleBound :
    (N : ℕ) -> (c : TransitionClass) -> Set

  transitionMagnitudeEnvelopeObligated :
    (N : ℕ) -> (c : TransitionClass) -> Set

  transitionRowAlphaProductBoundObligated :
    (N : ℕ) -> (c : TransitionClass) -> Set

  transitionColumnBetaProductBoundObligated :
    (N : ℕ) -> (c : TransitionClass) -> Set

  transitionBalancedRowN1BoundObligated :
    (N : ℕ) -> Set

  transitionBalancedColumnN1BoundObligated :
    (N : ℕ) -> Set

------------------------------------------------------------------------
-- Status summary.
--
-- This is a progress surface only. No closure is claimed here.

record TransitionPrimitiveEstimatesStatus : Set where
  constructor mkTransitionPrimitiveEstimatesStatus
  field
    incidenceClassified : Bool
    rowCountBoundProved : Bool
    columnCountBoundProved : Bool
    piProductScaleBoundProved : Bool
    magnitudeEnvelopeProved : Bool
    rowAlphaProductProved : Bool
    columnBetaProductProved : Bool
    exponentArithmeticInstalled : Bool
    balancedN1N1RouteStated : Bool

open TransitionPrimitiveEstimatesStatus public

currentTransitionPrimitiveEstimatesStatus :
  TransitionPrimitiveEstimatesStatus
currentTransitionPrimitiveEstimatesStatus =
  mkTransitionPrimitiveEstimatesStatus
    false
    false
    false
    false
    false
    false
    false
    true
    true
