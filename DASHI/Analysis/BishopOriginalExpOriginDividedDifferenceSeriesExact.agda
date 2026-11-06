{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalExpOriginDividedDifferenceSeriesExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP EXP: EXACT ORIGIN DIVIDED-DIFFERENCE SERIES.
--
-- Define Q(h)=Σ_{n>=0} h^n/(n+1)! using the literal pinned
-- Exp.inverseFactorial, the literal Bishop Sequence.SeriesOf and
-- Sequence.lim. For EVERY h the shifted series converges absolutely.
--
-- At EVERY finite stage:
--   Σ_{k< N+1} expTerm(h,k) ~= 1 + h Σ_{k<N} qTerm(h,k).
-- Passing to the two ORIGINAL Bishop limits yields the exact global
-- first-order division-free factorization
--   exp_B(h) - 1 ~= h Q(h).
--
-- This supplies a genuine source quotient function for the
-- origin derivative. The remaining analytic step is to prove
-- Q(h_j)->1 whenever h_j->0 (equivalently the shifted factorial
-- tail is continuous at zero). No division by h, postulates or
-- second exp carrier appear anywhere in this module.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpZero
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power

originalExpOriginQuotientTerm : R.ℝ → Nat → R.ℝ
originalExpOriginQuotientTerm h n =
  R._*_ (R.pow h n)
    (Exp.embed (Exp.inverseFactorial (suc n)))

originalExpOriginMagnitudeTerm : R.ℝ → Nat → R.ℝ
originalExpOriginMagnitudeTerm h n =
  R._*_
    (Exp.embed (Exp.inverseFactorial (suc n)))
    (R.∣ R.pow h n ∣)

originalExpOriginMagnitudeNonnegative :
  (h : R.ℝ) (n : Nat) →
  R.NonNegative (originalExpOriginMagnitudeTerm h n)
originalExpOriginMagnitudeNonnegative h n =
  RP.nonNegx,y⇒nonNegx*y
    (Exp.embeddedInverseFactorialNonnegative (suc n))
    (RP.nonNeg∣x∣ (R.pow h n))

originalExpOriginQuotientTermAbs :
  (h : R.ℝ) (n : Nat) →
  R._≃_
    (R.∣ originalExpOriginQuotientTerm h n ∣)
    (originalExpOriginMagnitudeTerm h n)
originalExpOriginQuotientTermAbs h n =
  RP.≃-trans
    (RP.∣x*y∣≃∣x∣*∣y∣
      (R.pow h n)
      (Exp.embed (Exp.inverseFactorial (suc n))))
    (RP.≃-trans
      (RP.*-cong
        RP.≃-refl
        (RP.nonNegx⇒∣x∣≃x
          (Exp.embeddedInverseFactorialNonnegative (suc n))))
      (RP.*-comm
        (R.∣ R.pow h n ∣)
        (Exp.embed (Exp.inverseFactorial (suc n)))))

originalExpOriginMagnitudeSuccessorFactor :
  (h : R.ℝ) (n : Nat) →
  R._≃_
    (originalExpOriginMagnitudeTerm h (suc n))
    (R._*_
      (R._*_ (R.∣ h ∣)
        (Exp.embed (Data.Rational.Unnormalised._/_ (Data.Integer.Base.+ 1) (suc (suc n)))))
      (originalExpOriginMagnitudeTerm h n))
originalExpOriginMagnitudeSuccessorFactor h n =
  RP.≃-trans
    (RP.*-cong
      (Exp.embeddedInverseFactorialSuccessor (suc n))
      (Seq.∣xⁿ∣≃∣x∣ⁿ h (suc n)))
    (RP.≃-trans
      (let open RP.ℝ-Solver in
       solve 4
         (λ reciprocal coefficient oldPower absH →
           ((reciprocal ⊗ coefficient) ⊗ (oldPower ⊗ absH))
           ⊜ ((absH ⊗ reciprocal) ⊗ (coefficient ⊗ oldPower)))
         RP.≃-refl
         (Exp.embed (Data.Rational.Unnormalised._/_ (Data.Integer.Base.+ 1) (suc (suc n))))
         (Exp.embed (Exp.inverseFactorial (suc n)))
         (R.pow (R.∣ h ∣) n)
         (R.∣ h ∣))
      (RP.*-cong
        RP.≃-refl
        (RP.*-congˡ
          (RP.≃-symm
            (Seq.∣xⁿ∣≃∣x∣ⁿ h n)))))

originalExpOriginMagnitudeRatioHalf :
  (h : R.ℝ) (n : Nat) →
  (2 * Exp.magnitudeNaturalBound h) Data.Nat.Base.≤ (suc (suc n)) →
  R._≤_
    (originalExpOriginMagnitudeTerm h (suc n))
    (R._*_ Exp.half (originalExpOriginMagnitudeTerm h n))
originalExpOriginMagnitudeRatioHalf h n cutoff =
  RP.≤-respˡ-≃
    (originalExpOriginMagnitudeSuccessorFactor h n)
    (RP.*-monoʳ-≤-nonNeg
      (Exp.magnitudeRatioBelowHalf h (suc n) cutoff)
      (originalExpOriginMagnitudeNonnegative h n))

originalExpOriginMagnitudeConvergent :
  (h : R.ℝ) →
  Seq._isConvergent
    (Seq.SeriesOf (originalExpOriginMagnitudeTerm h))
originalExpOriginMagnitudeConvergent h =
  Seq.proposition-3-6-1
    (Exp.halfPositive , Exp.halfBelowOne)
    (2 * Exp.magnitudeNaturalBound h ,
      λ n nAtLeast →
        originalExpOriginMagnitudeRatioHalf h n
          (Data.Nat.Properties.≤-trans
            nAtLeast
            (Data.Nat.Properties.n≤1+n (suc n))))

originalExpOriginQuotientAbsolutelyConvergent :
  (h : R.ℝ) →
  Seq.SeriesOf_ConvergesAbsolutely
    (originalExpOriginQuotientTerm h)
originalExpOriginQuotientAbsolutelyConvergent h =
  let
    majorant = originalExpOriginMagnitudeConvergent h
  in
  proj₁ majorant ,
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count) →
      RP.≃-symm
        (Ext.seriesPartialSumsCongruent
          (originalExpOriginQuotientTermAbs h) (suc count))})
    majorant

originalExpOriginQuotient : R.ℝ → R.ℝ
originalExpOriginQuotient h =
  Seq.lim
    (Seq.absolute⇒isConvergent
      (originalExpOriginQuotientAbsolutelyConvergent h))

originalExpOriginQuotientConverges :
  (h : R.ℝ) →
  Seq._ConvergesTo_
    (Seq.SeriesOf (originalExpOriginQuotientTerm h))
    (originalExpOriginQuotient h)
originalExpOriginQuotientConverges h =
  proj₂
    (Seq.absolute⇒isConvergent
      (originalExpOriginQuotientAbsolutelyConvergent h))

-- Literal factorial-shift finite identity, with no quotient division.
originalExpOriginSuccessorTerm :
  (h : R.ℝ) (n : Nat) →
  R._≃_
    (Exp.expTerm h (suc n))
    (R._*_ h (originalExpOriginQuotientTerm h n))
originalExpOriginSuccessorTerm h n =
  let open RP.ℝ-Solver in
  solve 3
    (λ oldPower h′ coeff →
      ((oldPower ⊗ h′) ⊗ coeff)
      ⊜ h′ ⊗ (oldPower ⊗ coeff))
    RP.≃-refl
    (R.pow h n) h (Exp.embed (Exp.inverseFactorial (suc n)))

originalExpOriginFiniteFactor :
  (h : R.ℝ) (n : Nat) →
  R._≃_
    (Seq.SeriesOf (Exp.expTerm h) (suc n))
    (R._+_
      R.1ℝ
      (R._*_ h
        (Seq.SeriesOf (originalExpOriginQuotientTerm h) n)))
originalExpOriginFiniteFactor h zero =
  let open RP.ℝ-Solver in
  solve 1
    (λ h′ →
      (Κ 0ℚᵘ ⊕ (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ))
      ⊜ Κ 1ℚᵘ ⊕ (h′ ⊗ Κ 0ℚᵘ))
    RP.≃-refl h
originalExpOriginFiniteFactor h (suc n) =
  RP.≃-trans
    (RP.+-cong
      (originalExpOriginFiniteFactor h n)
      (originalExpOriginSuccessorTerm h n))
    (let open RP.ℝ-Solver in
     solve 4
       (λ h′ partial quotient one →
         (one ⊕ (h′ ⊗ partial)) ⊕ (h′ ⊗ quotient)
         ⊜ one ⊕ (h′ ⊗ (partial ⊕ quotient)))
       RP.≃-refl
       h
       (Seq.SeriesOf (originalExpOriginQuotientTerm h) n)
       (originalExpOriginQuotientTerm h n)
       R.1ℝ)

originalExpOriginFiniteFactorLimit :
  (h : R.ℝ) →
  R._≃_
    (Exp.bishopExp h)
    (R._+_ R.1ℝ (R._*_ h (originalExpOriginQuotient h)))
originalExpOriginFiniteFactorLimit h =
  let
    leftConverges :
      Seq._ConvergesTo_
        (λ n → Seq.SeriesOf (Exp.expTerm h) (suc n))
        (Exp.bishopExp h)
    leftConverges =
      Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
        (Seq.shift-is-subsequence
          (Seq.SeriesOf (Exp.expTerm h)) 1)
        (Exp.bishopExp h , Exp.bishopExpConverges h)

    rightConverges :
      Seq._ConvergesTo_
        (λ n →
          R._+_ R.1ℝ
            (R._*_ h
              (Seq.SeriesOf (originalExpOriginQuotientTerm h) n)))
        (R._+_ R.1ℝ
          (R._*_ h (originalExpOriginQuotient h)))
    rightConverges =
      Seq.xₙ+yₙ→x₀+y₀
        (R.1ℝ , Power.constantConverges R.1ℝ)
        (R._*_ h (originalExpOriginQuotient h) ,
          Seq.xₙyₙ→x₀y₀
            (h , Power.constantConverges h)
            (originalExpOriginQuotient h ,
              originalExpOriginQuotientConverges h))
  in
  Seq.uniqueness-of-limits
    leftConverges
    (Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ {(suc n) →
        RP.≃-symm (originalExpOriginFiniteFactor h (suc n))})
      (R._+_ R.1ℝ (R._*_ h (originalExpOriginQuotient h)) ,
        rightConverges))

-- This is the precise nondivision origin factorisation demanded by
-- BishopFactorDerivativeAt, with the ACTUAL original exp_B.
originalExpOriginIncrementFactor :
  (h : R.ℝ) →
  R._≃_
    (R._-_ (Exp.bishopExp (R._+_ R.0ℝ h))
      (Exp.bishopExp R.0ℝ))
    (R._*_ h (originalExpOriginQuotient h))
originalExpOriginIncrementFactor h =
  RP.≃-trans
    (RP.+-cong
      (ExpCong.bishopExpCongruent (RP.+-identityˡ h))
      (RP.-‿cong ExpZero.bishopExpZero))
    (RP.≃-trans
      (originalExpOriginFiniteFactorLimit h)
      (let open RP.ℝ-Solver in
       solve 2
         (λ h′ quotient →
           (Κ 1ℚᵘ ⊕ (h′ ⊗ quotient)) ⊖ Κ 1ℚᵘ
           ⊜ h′ ⊗ quotient)
         RP.≃-refl h (originalExpOriginQuotient h)))
