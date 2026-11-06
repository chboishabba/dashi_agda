{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalExponentialUniformCompactTailExact where

------------------------------------------------------------------------
-- K04d-CONTINUITY: GENUINE ORIGINAL exp_B UNIFORM TAIL ON A BALL.
--
-- For a fixed Bishop-real M>=0, all ORIGINAL literal source terms
-- expTerm(x,n)=pow(x,n) * (1/n!) obey, whenever |x|<=M,
--
--   |expTerm(x,n)| <= expMagnitudeTerm(M,n).
--
-- The right-hand source majorant is already proved convergent by
-- the selected original Exp.expMagnitudeSeriesConvergent.
-- Cauchy's criterion supplies one N(k), INDEPENDENT of x, such that
--
--  |exp_B(x) - Σ_(n<N) expTerm(x,n)| <= 1/k
--
-- for all |x|<=M and all N >= N(k).
--
-- This module actually constructs that all-point uniform error via
-- Bishop finite sum triangle + comparison + original sum convergence
-- and Bishop closed-order-under-limits. It does NOT just declare
-- a UniformApproximation Set or supply a synthetic exp function.
--
-- This is the original source compact-uniform factorial series
-- approximation needed by the K04d original complex exp continuity.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Data.Nat.Base as N using (NonZero; _≤_; _≥_)
import Data.Nat.Properties as NP
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Analysis.BishopUniformLimitSequentialContinuityExact as Uniform

sourceExpAbsolutePowerBound :
  (bound : R.ℝ) →
  R.NonNegative bound →
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) bound →
  (degree : Nat) →
  R._≤_
    (R.∣ R.pow point degree ∣)
    (R.∣ R.pow bound degree ∣)
sourceExpAbsolutePowerBound bound boundNonnegative point inside degree =
  RP.≤-respˡ-≃
    (RP.≃-symm
      (Seq.∣xⁿ∣≃∣x∣ⁿ point degree))
    (RP.≤-respʳ-≃
      (RP.≃-symm
        (RP.nonNegx⇒∣x∣≃x
          (Seq.nonNegx⇒nonNegxⁿ degree boundNonnegative)))
      (Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ
        degree inside (RP.nonNeg∣x∣ point)))

sourceExpTermUniformMagnitude :
  (bound : R.ℝ) →
  R.NonNegative bound →
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) bound →
  (degree : Nat) →
  R._≤_
    (R.∣ Exp.expTerm point degree ∣)
    (Exp.expMagnitudeTerm bound degree)
sourceExpTermUniformMagnitude bound nn point inside degree =
  RP.≤-respˡ-≃
    (RP.≃-symm (Exp.expTermAbsIsMagnitude point degree))
    (RP.*-monoˡ-≤-nonNeg
      (sourceExpAbsolutePowerBound bound nn point inside degree)
      (Exp.embeddedInverseFactorialNonnegative degree))

-- Unlike the original pointwise ratio-test cutoff in Exp, this one
-- is chosen ONCE from a reference bound, then used for EVERY point
-- in the ball through the all-degree comparison proved above.
sourceExpUniformTailCutoff :
  (bound : R.ℝ) →
  (k : Nat) → .{{_ : NonZero k}} →
  Nat
sourceExpUniformTailCutoff bound k =
  suc (proj₁
    (Seq.cauchyConvergenceTest-if
      (Exp.expMagnitudeTerm bound)
      (Exp.expMagnitudeSeriesConvergent bound)
      k))

orderedSourceExpUniformFiniteTail :
  (bound : R.ℝ) →
  R.NonNegative bound →
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) bound →
  (k : Nat) → .{{_ : NonZero k}} →
  (m n : Nat) →
  m ≤ n →
  m ≥ sourceExpUniformTailCutoff bound k →
  n ≥ sourceExpUniformTailCutoff bound k →
  R._≤_
    (R.∣ Seq.∑ (Exp.expTerm point) m n ∣)
    (Uniform.inversePrecision k)
orderedSourceExpUniformFiniteTail bound nn point inside k
    m n m≤n mPast nPast =
  RP.≤-trans
    (Seq.∑-triangle-inequality (Exp.expTerm point) m n m≤n)
    (RP.≤-trans
      (Seq.∑-mono-≤
        (sourceExpTermUniformMagnitude bound nn point inside)
        m n m≤n)
      (RP.≤-trans
        (RP.x≤∣x∣ {x = Seq.∑ (Exp.expMagnitudeTerm bound) m n})
        (proj₂
          (Seq.cauchyConvergenceTest-if
            (Exp.expMagnitudeTerm bound)
            (Exp.expMagnitudeSeriesConvergent bound) k)
          m n mPast nPast)))

sourceExpUniformFiniteTail :
  (bound : R.ℝ) →
  R.NonNegative bound →
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) bound →
  (k : Nat) → .{{_ : NonZero k}} →
  (m n : Nat) →
  m ≥ sourceExpUniformTailCutoff bound k →
  n ≥ sourceExpUniformTailCutoff bound k →
  R._≤_
    (R.∣ Seq.∑ (Exp.expTerm point) m n ∣)
    (Uniform.inversePrecision k)
sourceExpUniformFiniteTail bound nn point inside k m n mPast nPast
    with NP.≤-total m n
... | inj₁ m≤n =
  orderedSourceExpUniformFiniteTail
    bound nn point inside k m n m≤n mPast nPast
... | inj₂ n≤m =
  RP.≤-respˡ-≃
    (RP.≃-trans
      (RP.≃-symm
        (RP.∣-x∣≃∣x∣ {x = Seq.∑ (Exp.expTerm point) m n}))
      (RP.∣-∣-cong
        (Seq.neg-flips-∑ (Exp.expTerm point) m n)))
    (orderedSourceExpUniformFiniteTail
      bound nn point inside k n m n≤m nPast mPast)

sourceExpFinitePartialMinusIsTail :
  (point : R.ℝ) (m n : Nat) →
  R._≃_
    (R._-_
      (Seq.SeriesOf (Exp.expTerm point) n)
      (Seq.SeriesOf (Exp.expTerm point) m))
    (Seq.∑ (Exp.expTerm point) m n)
sourceExpFinitePartialMinusIsTail point zero n =
  let open RP.ℝ-Solver
  in solve 1
    (λ prefix → prefix ⊖ Κ 0ℚᵘ ⊜ prefix)
    RP.≃-refl (Seq.SeriesOf (Exp.expTerm point) n)
sourceExpFinitePartialMinusIsTail point (suc m) n = RP.≃-refl

-- Original SOURCE exp(x) is definitionally the unique limit of the
-- selected Exp.expTerm series; never name a second "exp" evaluator.
sourceExpUniformLimitError :
  (bound : R.ℝ) →
  R.NonNegative bound →
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) bound →
  (k : Nat) → .{{_ : NonZero k}} →
  (m : Nat) →
  m ≥ sourceExpUniformTailCutoff bound k →
  R._≤_
    (R.∣
      R._-_
        (Exp.bishopExp point)
        (Seq.SeriesOf (Exp.expTerm point) m)
    ∣)
    (Uniform.inversePrecision k)
sourceExpUniformLimitError bound nn point inside k m mPast =
  let
    convergent =
      Seq.absolute⇒isConvergent
        (Exp.expAbsoluteSeriesConvergent point)
    cutoff = sourceExpUniformTailCutoff bound k
    partial = Seq.SeriesOf (Exp.expTerm point)
    limit = Exp.bishopExp point

    shifted : Nat → R.ℝ
    shifted n = partial (n + cutoff)

    shiftedConverges : Seq._ConvergesTo_ shifted limit
    shiftedConverges =
      Seq.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
        (Seq.subseq*
          ((λ n → n + cutoff)
          , (λ n → RP.≃-refl)
          , (λ n → NP.n<1+n (n + cutoff))))
        convergent

    constantNegative : Nat → R.ℝ
    constantNegative n = R.-_ (partial m)

    constantConverges : Seq._isConvergent constantNegative
    constantConverges =
      (R.-_ (partial m)) ,
      Seq.xₙ≃c⇒xₙ→c
        (λ {(suc n) → RP.≃-refl})

    differenceConverges :
      Seq._ConvergesTo_
        (λ n → R._-_ (shifted n) (partial m))
        (R._-_ limit (partial m))
    differenceConverges =
      Seq.xₙ+yₙ→x₀+y₀
        (limit , shiftedConverges)
        constantConverges

    absConvergent :
      Seq._isConvergent
        (λ n → R.∣ R._-_ (shifted n) (partial m) ∣)
    absConvergent =
      (R.∣ R._-_ limit (partial m) ∣) ,
      Seq.∣xₙ∣→∣x₀∣
        ((R._-_ limit (partial m)) , differenceConverges)

    boundEach : (n : Nat) →
      R._≤_
        (R.∣ R._-_ (shifted n) (partial m) ∣)
        (Uniform.inversePrecision k)
    boundEach n =
      RP.≤-respˡ-≃
        (RP.∣-∣-cong
          (sourceExpFinitePartialMinusIsTail point m (n + cutoff)))
        (sourceExpUniformFiniteTail
          bound nn point inside k m (n + cutoff)
          mPast (NP.m≤n+m cutoff n))
  in
  Seq.xₙ≤y⇒limxₙ≤y boundEach absConvergent

-- An all-point uniform original EXP approximation on each fixed ball,
-- with exactly one cutoff from the convergent reference majorant.
sourceExpUniformApproximationOnBall :
  (bound : R.ℝ) →
  R.NonNegative bound →
  (k : Nat) → .{{_ : NonZero k}} →
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) bound →
  R._≤_
    (R.∣
      R._-_
        (Seq.SeriesOf (Exp.expTerm point)
          (sourceExpUniformTailCutoff bound k))
        (Exp.bishopExp point)
    ∣)
    (Uniform.inversePrecision k)
sourceExpUniformApproximationOnBall bound nn k point inside =
  RP.≤-respˡ-≃
    (RP.∣x-y∣≃∣y-x∣
      (Exp.bishopExp point)
      (Seq.SeriesOf (Exp.expTerm point)
        (sourceExpUniformTailCutoff bound k)))
    (sourceExpUniformLimitError
      bound nn point inside
      k (sourceExpUniformTailCutoff bound k)
      NP.≤-refl)
