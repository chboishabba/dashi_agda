module DASHI.Physics.YangMills.BalabanWeightedNeumannRemainder where

------------------------------------------------------------------------
-- Quantitative bridge from a one-step weighted residual contraction to the
-- exact finite Neumann telescope.
--
-- The algebraic module BalabanFiniteNeumannParametrix proves that the depth-n
-- approximation has residual exactly R^n x.  This module adds the missing
-- finite quantitative induction:
--
--   ||R x||_mu <= rho ||x||_mu
--       implies
--   ||R^n x||_mu <= rho^n ||x||_mu.
--
-- No completeness or infinite-series convergence is asserted here.  The field
-- contractionStrict records the genuine analytic frontier rho < 1, while the
-- theorem below only uses the ordered-monoid laws required for the finite
-- power estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.BalabanFiniteNeumannParametrix
open import DASHI.Physics.YangMills.BalabanRandomWalkRemainderBound

record WeightedResidualContraction
  (Carrier Bound : Set)
  (bundle : AdditiveParametrixData Carrier)
  : Set₁ where
  field
    oneBound : Bound
    multiplyBound : Bound → Bound → Bound

    norm : Carrier → Bound
    LessEqual StrictLess : Bound → Bound → Set

    lessEqualRefl : ∀ value → LessEqual value value
    lessEqualTrans :
      ∀ {left middle right} →
      LessEqual left middle →
      LessEqual middle right →
      LessEqual left right

    multiplyMonotoneRight :
      ∀ prefix {left right} →
      LessEqual left right →
      LessEqual
        (multiplyBound prefix left)
        (multiplyBound prefix right)

    oneLeft : ∀ value → multiplyBound oneBound value ≡ value
    multiplyAssoc : ∀ left middle right →
      multiplyBound left (multiplyBound middle right)
        ≡ multiplyBound (multiplyBound left middle) right

    contractionFactor : Bound
    contractionStrict : StrictLess contractionFactor oneBound

    residualContracts : ∀ value →
      LessEqual
        (norm (residual bundle value))
        (multiplyBound contractionFactor (norm value))

open WeightedResidualContraction public

boundPower :
  ∀ {Carrier Bound bundle} →
  WeightedResidualContraction Carrier Bound bundle →
  Nat → Bound
boundPower control zero = oneBound control
boundPower control (suc depth) =
  multiplyBound control
    (boundPower control depth)
    (contractionFactor control)

weightedResidualPowerBound :
  ∀ {Carrier Bound} {bundle : AdditiveParametrixData Carrier}
  (control : WeightedResidualContraction Carrier Bound bundle) →
  ∀ depth value →
  LessEqual control
    (norm control (residualPower bundle depth value))
    (multiplyBound control
      (boundPower control depth)
      (norm control value))
weightedResidualPowerBound control zero value =
  subst
    (λ target → LessEqual control (norm control value) target)
    (sym (oneLeft control (norm control value)))
    (lessEqualRefl control (norm control value))
weightedResidualPowerBound {bundle = bundle} control (suc depth) value =
  subst
    (λ target →
      LessEqual control
        (norm control
          (residualPower bundle depth (residual bundle value)))
        target)
    (multiplyAssoc control
      (boundPower control depth)
      (contractionFactor control)
      (norm control value))
    (lessEqualTrans control
      (weightedResidualPowerBound control depth (residual bundle value))
      (multiplyMonotoneRight control
        (boundPower control depth)
        (residualContracts control value)))

finiteNeumannResidualControl :
  ∀ {Carrier Bound} {bundle : AdditiveParametrixData Carrier}
  (control : WeightedResidualContraction Carrier Bound bundle) →
  ∀ depth value →
  (operator bundle (finiteNeumannApproximation bundle depth value)
    ≡ subtract bundle value (residualPower bundle depth value))
  ×
  LessEqual control
    (norm control (residualPower bundle depth value))
    (multiplyBound control
      (boundPower control depth)
      (norm control value))
finiteNeumannResidualControl {bundle = bundle} control depth value =
  finiteRightNeumannTelescope bundle depth value
  , weightedResidualPowerBound control depth value

weightedRandomWalkRemainderBound :
  ∀ {Carrier Bound} {bundle : AdditiveParametrixData Carrier} →
  WeightedResidualContraction Carrier Bound bundle →
  Carrier →
  RandomWalkRemainderBound Carrier Bound
weightedRandomWalkRemainderBound {bundle = bundle} control value =
  record
    { remainder = λ depth → residualPower bundle depth value
    ; norm = norm control
    ; majorant = λ depth →
        multiplyBound control
          (boundPower control depth)
          (norm control value)
    ; LessEqual = LessEqual control
    ; bound = λ depth → weightedResidualPowerBound control depth value
    }
