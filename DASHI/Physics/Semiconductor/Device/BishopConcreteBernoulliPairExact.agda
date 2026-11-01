{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.BishopConcreteBernoulliPairExact where

------------------------------------------------------------------------
-- CONCRETE TWO-ORIENTATION BISHOP BERNOULLI PAIR
--
-- For 0 < x <= 1, existing repository theorems give
--
--   1 < exp(x)
--   exp(-x) < 1.
--
-- Hence both Bernoulli denominators are constructively nonzero:
--
--   exp(x)-1  > 0,
--   exp(-x)-1 < 0.
--
-- No point-local denominator authority field remains on this interval.
------------------------------------------------------------------------

open import Data.Rational.Unnormalised using (1ℚᵘ)
open import Data.Sum.Base using (inj₁; inj₂)

import Real as BishopReal
import RealProperties as BishopP
import Inverse as BishopInverse

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialMinusOnePositiveExact as Gap
import DASHI.Foundations.BishopNegativeExponentialUnitIntervalExact as NegExp
open import DASHI.Physics.YangMills.CompactLieProofLevel

forwardDenominator : BishopReal.ℝ → BishopReal.ℝ
forwardDenominator = Gap.expMinusOne

backwardDenominator : BishopReal.ℝ → BishopReal.ℝ
backwardDenominator x =
  BishopReal._-_ (Exp.bishopExp (BishopReal.- x)) BishopReal.1ℝ

backwardDenominatorNegative :
  ∀ {x : BishopReal.ℝ} →
  NegExp.PositiveUnitIntervalPoint x →
  BishopReal._<_ (backwardDenominator x) BishopReal.0ℝ
backwardDenominatorNegative {x} inputs =
  let
    expBelowOne = NegExp.negativeExpBelowOne inputs

    shifted =
      BishopP.+-monoʳ-<
        (BishopReal.- BishopReal.1ℝ)
        expBelowOne

    leftGap :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal.- BishopReal.1ℝ)
          (Exp.bishopExp (BishopReal.- x)))
        (backwardDenominator x)
    leftGap =
      let open BishopP.ℝ-Solver
      in solve 1
        (λ e → ((⊝ Κ 1ℚᵘ) ⊕ e) ⊜ (e ⊖ Κ 1ℚᵘ))
        BishopP.≃-refl
        (Exp.bishopExp (BishopReal.- x))

    rightZero :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal.- BishopReal.1ℝ)
          BishopReal.1ℝ)
        BishopReal.0ℝ
    rightZero =
      let open BishopP.ℝ-Solver
      in solve 0
        ((⊝ Κ 1ℚᵘ) ⊕ Κ 1ℚᵘ ⊜ Κ 0ℚᵘ)
        BishopP.≃-refl
  in
  BishopP.<-respʳ-≃ rightZero
    (BishopP.<-respˡ-≃ leftGap shifted)

backwardDenominatorNonzero :
  ∀ {x : BishopReal.ℝ} →
  NegExp.PositiveUnitIntervalPoint x →
  BishopReal._≄0 (backwardDenominator x)
backwardDenominatorNonzero inputs =
  inj₁ (backwardDenominatorNegative inputs)

forwardWeight :
  ∀ {x : BishopReal.ℝ} →
  NegExp.PositiveUnitIntervalPoint x →
  BishopReal.ℝ
forwardWeight {x} inputs =
  BishopReal._*_
    x
    (BishopInverse._⁻¹
      (forwardDenominator x)
      (Gap.expMinusOneNonzero (NegExp.positive inputs)))

backwardWeight :
  ∀ {x : BishopReal.ℝ} →
  NegExp.PositiveUnitIntervalPoint x →
  BishopReal.ℝ
backwardWeight {x} inputs =
  BishopReal._*_
    (BishopReal.- x)
    (BishopInverse._⁻¹
      (backwardDenominator x)
      (backwardDenominatorNonzero inputs))

forwardWeightCancels :
  ∀ {x : BishopReal.ℝ} →
  (inputs : NegExp.PositiveUnitIntervalPoint x) →
  BishopReal._≃_
    (BishopReal._*_
      (forwardWeight inputs)
      (forwardDenominator x))
    x
forwardWeightCancels {x} inputs =
  let
    d = forwardDenominator x
    nz = Gap.expMinusOneNonzero (NegExp.positive inputs)
    inverseLaw = BishopInverse.*-inverseˡ d nz
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 3
      (λ p i denominator →
        (p ⊗ i) ⊗ denominator ⊜ p ⊗ (i ⊗ denominator))
      BishopP.≃-refl
      x (BishopInverse._⁻¹ d nz) d)
    (BishopP.≃-trans
      (BishopP.*-congˡ inverseLaw)
      (BishopP.*-identityʳ x))

backwardWeightCancels :
  ∀ {x : BishopReal.ℝ} →
  (inputs : NegExp.PositiveUnitIntervalPoint x) →
  BishopReal._≃_
    (BishopReal._*_
      (backwardWeight inputs)
      (backwardDenominator x))
    (BishopReal.- x)
backwardWeightCancels {x} inputs =
  let
    d = backwardDenominator x
    nz = backwardDenominatorNonzero inputs
    inverseLaw = BishopInverse.*-inverseˡ d nz
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 3
      (λ p i denominator →
        (p ⊗ i) ⊗ denominator ⊜ p ⊗ (i ⊗ denominator))
      BishopP.≃-refl
      (BishopReal.- x) (BishopInverse._⁻¹ d nz) d)
    (BishopP.≃-trans
      (BishopP.*-congˡ inverseLaw)
      (BishopP.*-identityʳ (BishopReal.- x)))

record ConcreteBishopSGWeightPair : Set₁ where
  constructor concreteBishopSGWeightPair
  field
    drop : BishopReal.ℝ
    dropInPositiveUnitInterval : NegExp.PositiveUnitIntervalPoint drop

open ConcreteBishopSGWeightPair public

concreteForwardWeight : ConcreteBishopSGWeightPair → BishopReal.ℝ
concreteForwardWeight pair =
  forwardWeight (dropInPositiveUnitInterval pair)

concreteBackwardWeight : ConcreteBishopSGWeightPair → BishopReal.ℝ
concreteBackwardWeight pair =
  backwardWeight (dropInPositiveUnitInterval pair)

bishopConcreteBernoulliPairLevel : ProofLevel
bishopConcreteBernoulliPairLevel = machineChecked

-- Remaining analytic leaf:
-- a theorem relating the two orientations (for example the standard Bernoulli
-- identity) is useful for simplification, but it is no longer required merely
-- to construct either weight or to prove denominator nonzeroness.
