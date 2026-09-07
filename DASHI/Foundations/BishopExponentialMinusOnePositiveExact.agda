{-# OPTIONS --safe #-}

module DASHI.Foundations.BishopExponentialMinusOnePositiveExact where

------------------------------------------------------------------------
-- POSITIVE EXPONENTIAL GAP
--
-- Reuse the already checked concrete Bishop exponential order theorem:
--
--   0 < x  ->  1 < exp(x)
--
-- and translate it through subtraction to obtain the exact denominator fact
-- consumed by Bernoulli / Scharfetter-Gummel weights:
--
--   0 < exp(x) - 1.
------------------------------------------------------------------------

open import Data.Rational.Unnormalised using (1ℚᵘ)
open import Data.Sum.Base using (inj₂)

import Real as BishopReal
import RealProperties as BishopP
import Inverse as BishopInverse

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as PositiveExp
open import DASHI.Physics.YangMills.CompactLieProofLevel

expMinusOne : BishopReal.ℝ → BishopReal.ℝ
expMinusOne x = BishopReal._-_ (Exp.bishopExp x) BishopReal.1ℝ

expMinusOnePositive :
  ∀ {x : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ BishopReal.0ℝ (expMinusOne x)
expMinusOnePositive {x} xPositive =
  let
    oneBelowExp = PositiveExp.bishopExpStrictlyAboveOneOnPositive xPositive

    shifted =
      BishopP.+-monoʳ-<
        (BishopReal.- BishopReal.1ℝ)
        oneBelowExp

    leftZero :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal.- BishopReal.1ℝ)
          BishopReal.1ℝ)
        BishopReal.0ℝ
    leftZero =
      let open BishopP.ℝ-Solver
      in solve 0
        ((⊝ Κ 1ℚᵘ) ⊕ Κ 1ℚᵘ ⊜ Κ 0ℚᵘ)
        BishopP.≃-refl

    rightGap :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal.- BishopReal.1ℝ)
          (Exp.bishopExp x))
        (expMinusOne x)
    rightGap =
      let open BishopP.ℝ-Solver
      in solve 1
        (λ e → ((⊝ Κ 1ℚᵘ) ⊕ e) ⊜ (e ⊖ Κ 1ℚᵘ))
        BishopP.≃-refl
        (Exp.bishopExp x)
  in
  BishopP.<-respʳ-≃ rightGap
    (BishopP.<-respˡ-≃ leftZero shifted)

expMinusOneNonzero :
  ∀ {x : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._≄0 (expMinusOne x)
expMinusOneNonzero xPositive = inj₂ (expMinusOnePositive xPositive)

expMinusOneInverse :
  ∀ {x : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal.ℝ
expMinusOneInverse {x} xPositive =
  BishopInverse._⁻¹ (expMinusOne x) (expMinusOneNonzero xPositive)

expMinusOneInversePositive :
  ∀ {x : BishopReal.ℝ} →
  (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  BishopReal._<_ BishopReal.0ℝ (expMinusOneInverse xPositive)
expMinusOneInversePositive xPositive =
  BishopInverse.0<x⇒0<x⁻¹
    (expMinusOneNonzero xPositive)
    (expMinusOnePositive xPositive)

bishopExponentialMinusOnePositiveLevel : ProofLevel
bishopExponentialMinusOnePositiveLevel = machineChecked
