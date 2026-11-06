{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalExpOriginDerivativeClosedExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP EXP: CLOSED ORIGIN FACTOR DERIVATIVE.
--
-- Previous source owner constructs Q(h) from the ACTUAL shifted
-- factorial series and proves exp_B(h)-1 ~= h Q(h).
--
-- Here no differentiability-of-limit theorem is imported. Instead:
--
--   1/(n+1)! <= 1/n!
--     -> |Q(h)-1| <= exp_B(|h|)-1
--     -> Q(h_j) -> 1 whenever h_j -> 0
--
-- by ORIGINAL Bishop exp sequential continuity, source finite
-- sum triangle and comparison, genuine convergence of both series,
-- and the repository's vanishing-difference convergence theorem.
--
-- Thus `BishopFactorDerivativeAt Exp.bishopExp 0 1` is genuinely
-- constructed and fed into the source-native exponential Cauchy
-- product theorem to obtain exp'_B(x)=exp_B(x) at EVERY x.
--
-- No added Set oracle, postulates, synthetic exp, generic theorem
-- authority, or division by an arbitrary Bishop perturbation.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Data.Nat.Base as N

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as NatRecip
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialCauchyProductExact as ExpProduct
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpZero
import DASHI.Analysis.BishopOriginalExponentialSequentialContinuityExact as ExpCont
import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopOriginalExpOriginDividedDifferenceSeriesExact as Origin
import DASHI.Analysis.BishopOriginalExponentialGlobalDerivativeFromOriginExact as Global
import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as Vanish

originalInverseFactorialNonIncreasing :
  (n : Nat) →
  R._≤_
    (Exp.embed (Exp.inverseFactorial (suc n)))
    (Exp.embed (Exp.inverseFactorial n))
originalInverseFactorialNonIncreasing n =
  RP.≤-respˡ-≃
    (Exp.embeddedInverseFactorialSuccessor n)
    (RP.≤-respʳ-≃
      (RP.*-identityˡ
        (Exp.embed (Exp.inverseFactorial n)))
      (RP.*-monoˡ-≤-nonNeg
        (NatRecip.reciprocalAtMostOne n)
        (Exp.embeddedInverseFactorialNonnegative n)))

originalOriginQuotientMagnitudeBelowExpMagnitude :
  (h : R.ℝ) (n : Nat) →
  R._≤_
    (Origin.originalExpOriginMagnitudeTerm h n)
    (Exp.expMagnitudeTerm h n)
originalOriginQuotientMagnitudeBelowExpMagnitude h n =
  RP.*-monoˡ-≤-nonNeg
    (originalInverseFactorialNonIncreasing n)
    (RP.nonNeg∣x∣ (R.pow h n))

originalOriginQuotientTermBelowExpAtAbs :
  (h : R.ℝ) (n : Nat) →
  R._≤_
    (R.∣ Origin.originalExpOriginQuotientTerm h n ∣)
    (Exp.expTerm (R.∣ h ∣) n)
originalOriginQuotientTermBelowExpAtAbs h n =
  RP.≤-respˡ-≃
    (Origin.originalExpOriginQuotientTermAbs h n)
    (RP.≤-respʳ-≃
      (RP.≃-trans
        (RP.≃-symm (Exp.expTermAbsIsMagnitude h n))
        (ExpProduct.absoluteExpTermIsExpAbs h n))
      (originalOriginQuotientMagnitudeBelowExpMagnitude h n))

-- Remove the first coefficient, but keep the original Nat indexing.
-- Both original first coefficients are exactly one.
tailAfterOne : (Nat → R.ℝ) → Nat → R.ℝ
tailAfterOne term zero = R.0ℝ
tailAfterOne term (suc n) = term (suc n)

originalOriginQuotientHeadIsOne :
  (h : R.ℝ) →
  R._≃_ (Origin.originalExpOriginQuotientTerm h zero) R.1ℝ
originalOriginQuotientHeadIsOne h =
  let open RP.ℝ-Solver in
  solve 0
    (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ ⊜ Κ 1ℚᵘ)
    RP.≃-refl

originalExpAtAbsHeadIsOne :
  (h : R.ℝ) →
  R._≃_ (Exp.expTerm (R.∣ h ∣) zero) R.1ℝ
originalExpAtAbsHeadIsOne h =
  let open RP.ℝ-Solver in
  solve 0
    (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ ⊜ Κ 1ℚᵘ)
    RP.≃-refl

-- Generic finite first-coefficient removal, including exact index
-- behavior, rather than a second summation semantics.
tailAfterOneFinite :
  (term : Nat → R.ℝ) →
  R._≃_ (term zero) R.1ℝ →
  (n : Nat) →
  R._≃_
    (R._-_ (Seq.SeriesOf term (suc n)) R.1ℝ)
    (Seq.SeriesOf (tailAfterOne term) (suc n))
tailAfterOneFinite term firstIsOne zero =
  RP.≃-trans
    (RP.+-cong
      (RP.+-cong RP.≃-refl firstIsOne)
      RP.≃-refl)
    (let open RP.ℝ-Solver in
     solve 0
       ((Κ 0ℚᵘ ⊕ Κ 1ℚᵘ) ⊖ Κ 1ℚᵘ
         ⊜ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ)
       RP.≃-refl)
tailAfterOneFinite term firstIsOne (suc n) =
  RP.≃-trans
    (let open RP.ℝ-Solver in
     solve 3
       (λ partial next one →
         (partial ⊕ next) ⊖ one
         ⊜ (partial ⊖ one) ⊕ next)
       RP.≃-refl
       (Seq.SeriesOf term (suc n))
       (term (suc n))
       R.1ℝ)
    (RP.+-cong
      (tailAfterOneFinite term firstIsOne n)
      RP.≃-refl)

-- The discarded-head series limit is the actual original limit
-- minus one, by the PINNED convergence algebra.
tailAfterOneShiftConverges :
  (term : Nat → R.ℝ) →
  (firstIsOne : R._≃_ (term zero) R.1ℝ) →
  (limit : R.ℝ) →
  Seq._ConvergesTo_ (Seq.SeriesOf term) limit →
  Seq._ConvergesTo_
    (λ n → Seq.SeriesOf (tailAfterOne term) (suc n))
    (R._-_ limit R.1ℝ)
tailAfterOneShiftConverges term firstIsOne limit originalConverges =
  let
    shiftConverges :
      Seq._ConvergesTo_
        (λ n → Seq.SeriesOf term (suc n)) limit
    shiftConverges =
      Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
        (Seq.shift-is-subsequence (Seq.SeriesOf term) 1)
        (limit , originalConverges)

    differenceConverges :
      Seq._ConvergesTo_
        (λ n → R._-_ (Seq.SeriesOf term (suc n)) R.1ℝ)
        (R._-_ limit R.1ℝ)
    differenceConverges =
      Seq.xₙ+yₙ→x₀+y₀
        (limit , shiftConverges)
        (R.-_ R.1ℝ , Power.constantConverges (R.-_ R.1ℝ))
  in
  Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) → tailAfterOneFinite term firstIsOne (suc n)})
    (R._-_ limit R.1ℝ , differenceConverges)

originalExpQuotientTailTermBound :
  (h : R.ℝ) (n : Nat) →
  R._≤_
    (R.∣ tailAfterOne
      (Origin.originalExpOriginQuotientTerm h) n ∣)
    (tailAfterOne
      (Exp.expTerm (R.∣ h ∣)) n)
originalExpQuotientTailTermBound h zero =
  RP.≤-reflexive
    (RP.nonNegx⇒∣x∣≃x
      (RP.0≤x⇒nonNegx RP.≤-refl))
originalExpQuotientTailTermBound h (suc n) =
  originalOriginQuotientTermBelowExpAtAbs h (suc n)

originalExpQuotientTailPartialBound :
  (h : R.ℝ) (count : Nat) →
  R._≤_
    (R.∣ Seq.SeriesOf
      (tailAfterOne (Origin.originalExpOriginQuotientTerm h))
      (suc count) ∣)
    (Seq.SeriesOf
      (tailAfterOne (Exp.expTerm (R.∣ h ∣)))
      (suc count))
originalExpQuotientTailPartialBound h count =
  RP.≤-trans
    (Seq.∑-triangle-inequality
      (tailAfterOne (Origin.originalExpOriginQuotientTerm h))
      zero (suc count) N.z≤n)
    (Seq.∑-mono-≤
      (originalExpQuotientTailTermBound h)
      zero (suc count) N.z≤n)

originalExpQuotientMinusOneAbsBound :
  (h : R.ℝ) →
  R._≤_
    (R.∣ R._-_ (Origin.originalExpOriginQuotient h) R.1ℝ ∣)
    (R._-_ (Exp.bishopExp (R.∣ h ∣)) R.1ℝ)
originalExpQuotientMinusOneAbsBound h =
  let
    qConverges =
      tailAfterOneShiftConverges
        (Origin.originalExpOriginQuotientTerm h)
        (originalOriginQuotientHeadIsOne h)
        (Origin.originalExpOriginQuotient h)
        (Origin.originalExpOriginQuotientConverges h)

    expConverges =
      tailAfterOneShiftConverges
        (Exp.expTerm (R.∣ h ∣))
        (originalExpAtAbsHeadIsOne h)
        (Exp.bishopExp (R.∣ h ∣))
        (Exp.bishopExpConverges (R.∣ h ∣))
  in
  Seq.xₙ≤yₙ⇒limxₙ≤limyₙ
    (originalExpQuotientTailPartialBound h)
    (R.∣ R._-_ (Origin.originalExpOriginQuotient h) R.1ℝ ∣ ,
      Seq.∣xₙ∣→∣x₀∣
        (R._-_ (Origin.originalExpOriginQuotient h) R.1ℝ ,
          qConverges))
    (R._-_ (Exp.bishopExp (R.∣ h ∣)) R.1ℝ ,
      expConverges)

-- The bound's right side tends to zero on EVERY native Bishop null
-- sequence, because actual source exp_B is already sequentially
-- continuous and exp_B(0)=1.
originalExpOriginErrorConvergesZero :
  ∀ {perturbation : Nat → R.ℝ} →
  Seq._ConvergesTo_ perturbation R.0ℝ →
  Seq._ConvergesTo_
    (λ n → R._-_ (Exp.bishopExp (R.∣ perturbation n ∣)) R.1ℝ)
    R.0ℝ
originalExpOriginErrorConvergesZero
    {perturbation} perturbationConverges =
  let
    absZero : R._≃_ (R.∣ R.0ℝ ∣) R.0ℝ
    absZero =
      RP.nonNegx⇒∣x∣≃x
        (RP.0≤x⇒nonNegx RP.≤-refl)

    absConverges : Seq._ConvergesTo_
      (λ n → R.∣ perturbation n ∣) R.0ℝ
    absConverges =
      Seq.xₙ→x∧x≃y⇒xₙ→y
        (Seq.∣xₙ∣→∣x₀∣
          (R.0ℝ , perturbationConverges))
        absZero

    expConverges :
      Seq._ConvergesTo_
        (λ n → Exp.bishopExp (R.∣ perturbation n ∣))
        R.1ℝ
    expConverges =
      Seq.xₙ→x∧x≃y⇒xₙ→y
        (ExpCont.originalBishopExpSequentiallyContinuous
          (λ n → R.∣ perturbation n ∣)
          R.0ℝ absConverges)
        ExpZero.bishopExpZero
  in
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.xₙ+yₙ→x₀+y₀
      (R.1ℝ , expConverges)
      (R.-_ R.1ℝ , Power.constantConverges (R.-_ R.1ℝ)))
    (RP.+-inverseʳ R.1ℝ)

-- The ORIGINAL quotient series converges to 1 on EVERY null sequence.
-- This finishes the nondivision factor-derivative semantics at 0.
originalExpOriginQuotientConvergesToOne :
  ∀ {perturbation : Nat → R.ℝ} →
  Seq._ConvergesTo_ perturbation R.0ℝ →
  Seq._ConvergesTo_
    (λ n → Origin.originalExpOriginQuotient (perturbation n))
    R.1ℝ
originalExpOriginQuotientConvergesToOne
    {perturbation} perturbationConverges =
  Vanish.vanishingDifferenceConvergence
    (Power.constantConverges R.1ℝ)
    (originalExpOriginErrorConvergesZero perturbationConverges)
    (λ n →
      RP.≤-trans
        (originalExpQuotientMinusOneAbsBound (perturbation n))
        (RP.x≤∣x∣
          {x = R._-_
            (Exp.bishopExp (R.∣ perturbation n ∣)) R.1ℝ}))

originalBishopExpFactorDerivativeAtOrigin :
  Factor.BishopFactorDerivativeAt
    Exp.bishopExp R.0ℝ R.1ℝ
originalBishopExpFactorDerivativeAtOrigin = record
  { Factor.quotient = Origin.originalExpOriginQuotient
  ; Factor.incrementFactorisation = Origin.originalExpOriginIncrementFactor
  ; Factor.quotientConvergesOnNullSequences =
      originalExpOriginQuotientConvergesToOne
  }

-- All-real source exp differentiation is now derived, WITHOUT the
-- generic power-series differentiation-interchange axiom.
originalBishopExponentialFactorDerivative :
  (x : R.ℝ) →
  Factor.BishopFactorDerivativeAt
    Exp.bishopExp x (Exp.bishopExp x)
originalBishopExponentialFactorDerivative =
  Global.originalBishopExpGlobalFactorDerivativeFromOrigin
    originalBishopExpFactorDerivativeAtOrigin
