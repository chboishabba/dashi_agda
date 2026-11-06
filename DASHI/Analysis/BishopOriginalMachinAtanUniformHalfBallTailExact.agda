{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalMachinAtanUniformHalfBallTailExact where

------------------------------------------------------------------------
-- K05-PI: SOURCE-NATIVE UNIFORM ATAN LIMIT ON THE ACTUAL HALF-BALL.
--
-- All |t| <= 1/2 share ONE pinned Bishop Cauchy modulus for the
-- literal alternating Machin atan series:
--   atanSignedTerm t n = (-1)^n * t^(2n+1)/(2n+1).
--
-- The majorant is the *actual* original magnitude-term series at
-- t=1/2. Its ratio bound <= 1/4 is already established in
-- BishopMachinArctanConstructionExact.
--
-- Unlike a pointwise ratio test, the selected cutoff is independent
-- of the argument t. The theorem owns an error bound to the actual
-- Bishop atan limit, useful at both literal 1/5 and 1/239.
--
-- This is NOT the source atan-to-Cayley evaluation. That further
-- requires the original nested exponential/composition identity,
-- which must not be inferred from finite coefficient agreement.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Data.Nat.Base as N using (NonZero; _≤_; _≥_)
import Data.Nat.Properties as NP
open import Data.Product.Base using (proj₁; proj₂; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Exponents
import DASHI.Analysis.BishopUniformLimitSequentialContinuityExact as Uniform

originalHalfNonnegative : R.NonNegative Half.bishopHalf
originalHalfNonnegative =
  RP.0≤x⇒nonNegx
    (RP.≤-trans
      (RP.nonNegx⇒0≤x Atan.oneFifthNonnegative)
      (RP.≤-respˡ-≃
        (RP.≃-symm
          (RP.nonNegx⇒∣x∣≃x Atan.oneFifthNonnegative))
        Atan.bishopOneFifthInsideHalf))

originalHalfInsideHalf :
  R._≤_ (R.∣ Half.bishopHalf ∣) Half.bishopHalf
originalHalfInsideHalf =
  RP.≤-reflexive
    (RP.nonNegx⇒∣x∣≃x originalHalfNonnegative)

originalAtanMagnitudePowerBelowHalf :
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) Half.bishopHalf →
  (n : Nat) →
  R._≤_
    (R.∣ R.pow point (Exponents.oddExponent n) ∣)
    (R.∣ R.pow Half.bishopHalf (Exponents.oddExponent n) ∣)
originalAtanMagnitudePowerBelowHalf point inside n =
  RP.≤-trans
    (RP.≤-respˡ-≃
      (RP.≃-symm
        (Seq.∣xⁿ∣≃∣x∣ⁿ point (Exponents.oddExponent n)))
      (Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ
        (Exponents.oddExponent n)
        inside (RP.nonNeg∣x∣ point)))
    (RP.x≤∣x∣
      {x = R.pow Half.bishopHalf (Exponents.oddExponent n)})

originalAtanMagnitudeBelowHalfReference :
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) Half.bishopHalf →
  (n : Nat) →
  R._≤_
    (Atan.atanMagnitudeTerm point n)
    (Atan.atanMagnitudeTerm Half.bishopHalf n)
originalAtanMagnitudeBelowHalfReference point inside n =
  RP.*-mono-≤
    (Atan.embeddedInverseOddNonnegative n)
    (RP.nonNeg∣x∣
      (R.pow point (Exponents.oddExponent n)))
    RP.≤-refl
    (originalAtanMagnitudePowerBelowHalf point inside n)

originalAtanSignedAbsoluteBelowHalfReference :
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) Half.bishopHalf →
  (n : Nat) →
  R._≤_
    (R.∣ Atan.atanSignedTerm point n ∣)
    (Atan.atanMagnitudeTerm Half.bishopHalf n)
originalAtanSignedAbsoluteBelowHalfReference point inside n =
  RP.≤-respˡ-≃
    (Atan.atanSignedAbsIsMagnitude point n)
    (originalAtanMagnitudeBelowHalfReference point inside n)

-- The selected majorant is an original signed-term magnitude series,
-- rather than an unrelated geometric proxy.
originalAtanHalfMajorantConvergent :
  Seq._isConvergent
    (Seq.SeriesOf (Atan.atanMagnitudeTerm Half.bishopHalf))
originalAtanHalfMajorantConvergent =
  Seq.proposition-3-6-1
    (Atan.quarterPositive , Atan.quarterBelowOne)
    (zero , λ n _ →
      Atan.atanMagnitudeSuccessorBelowQuarter
        Half.bishopHalf n originalHalfInsideHalf)

sourceAtanUniformTailCutoff :
  (k : Nat) → .{{_ : NonZero k}} → Nat
sourceAtanUniformTailCutoff k =
  suc (proj₁
    (Seq.cauchyConvergenceTest-if
      (Atan.atanMagnitudeTerm Half.bishopHalf)
      originalAtanHalfMajorantConvergent k))

sourceAtanUniformOrderedFiniteTail :
  (point : R.ℝ) →
  (inside : R._≤_ (R.∣ point ∣) Half.bishopHalf) →
  (k : Nat) → .{{_ : NonZero k}} →
  (m n : Nat) →
  m ≤ n →
  m ≥ sourceAtanUniformTailCutoff k →
  n ≥ sourceAtanUniformTailCutoff k →
  R._≤_
    (R.∣ Seq.∑ (Atan.atanSignedTerm point) m n ∣)
    (Uniform.inversePrecision k)
sourceAtanUniformOrderedFiniteTail point inside k
    m n ordered mPast nPast =
  RP.≤-trans
    (Seq.∑-triangle-inequality
      (Atan.atanSignedTerm point) m n ordered)
    (RP.≤-trans
      (Seq.∑-mono-≤
        (originalAtanSignedAbsoluteBelowHalfReference point inside)
        m n ordered)
      (RP.≤-trans
        (RP.x≤∣x∣
          {x = Seq.∑ (Atan.atanMagnitudeTerm Half.bishopHalf) m n})
        (proj₂
          (Seq.cauchyConvergenceTest-if
            (Atan.atanMagnitudeTerm Half.bishopHalf)
            originalAtanHalfMajorantConvergent k)
          m n mPast nPast)))

sourceAtanUniformFiniteTail :
  (point : R.ℝ) →
  (inside : R._≤_ (R.∣ point ∣) Half.bishopHalf) →
  (k : Nat) → .{{_ : NonZero k}} →
  (m n : Nat) →
  m ≥ sourceAtanUniformTailCutoff k →
  n ≥ sourceAtanUniformTailCutoff k →
  R._≤_
    (R.∣ Seq.∑ (Atan.atanSignedTerm point) m n ∣)
    (Uniform.inversePrecision k)
sourceAtanUniformFiniteTail point inside k
    m n mPast nPast with NP.≤-total m n
... | inj₁ ordered =
  sourceAtanUniformOrderedFiniteTail
    point inside k m n ordered mPast nPast
... | inj₂ ordered =
  RP.≤-respˡ-≃
    (RP.≃-trans
      (RP.≃-symm
        (RP.∣-x∣≃∣x∣
          {x = Seq.∑ (Atan.atanSignedTerm point) m n}))
      (RP.∣-∣-cong
        (Seq.neg-flips-∑
          (Atan.atanSignedTerm point) m n)))
    (sourceAtanUniformOrderedFiniteTail
      point inside k n m ordered nPast mPast)

sourceAtanPartialMinusIsTail :
  (point : R.ℝ) (m n : Nat) →
  R._≃_
    (R._-_
      (Seq.SeriesOf (Atan.atanSignedTerm point) n)
      (Seq.SeriesOf (Atan.atanSignedTerm point) m))
    (Seq.∑ (Atan.atanSignedTerm point) m n)
sourceAtanPartialMinusIsTail point zero n =
  let open RP.ℝ-Solver in
  solve 1
    (λ prefix → prefix ⊖ Κ 0ℚᵘ ⊜ prefix)
    RP.≃-refl
    (Seq.SeriesOf (Atan.atanSignedTerm point) n)
sourceAtanPartialMinusIsTail point (suc m) n =
  RP.≃-refl

sourceAtanUniformLimitError :
  (point : R.ℝ) →
  (inside : R._≤_ (R.∣ point ∣) Half.bishopHalf) →
  (k : Nat) → .{{_ : NonZero k}} →
  (m : Nat) →
  m ≥ sourceAtanUniformTailCutoff k →
  R._≤_
    (R.∣
      R._-_
        (Atan.bishopAtanHalfBall point inside)
        (Seq.SeriesOf (Atan.atanSignedTerm point) m)
    ∣)
    (Uniform.inversePrecision k)
sourceAtanUniformLimitError point inside k m mPast =
  let
    cutoff = sourceAtanUniformTailCutoff k
    partial = Seq.SeriesOf (Atan.atanSignedTerm point)
    limit = Atan.bishopAtanHalfBall point inside

    shifted : Nat → R.ℝ
    shifted n = partial (n + cutoff)

    shiftedConverges : Seq._ConvergesTo_ shifted limit
    shiftedConverges =
      Seq.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
        (Seq.subseq*
          ((λ n → n + cutoff)
          , (λ n → RP.≃-refl)
          , (λ n → NP.n<1+n (n + cutoff))))
        (limit , Atan.bishopAtanHalfBallConverges point inside)

    negPartialConverges : Seq._isConvergent
      (λ _ → R.-_ (partial m))
    negPartialConverges =
      R.-_ (partial m) ,
      Seq.xₙ≃c⇒xₙ→c (λ {(suc n) → RP.≃-refl})

    differenceConverges :
      Seq._ConvergesTo_
        (λ n → R._-_ (shifted n) (partial m))
        (R._-_ limit (partial m))
    differenceConverges =
      Seq.xₙ+yₙ→x₀+y₀
        (limit , shiftedConverges)
        negPartialConverges

    absConvergent : Seq._isConvergent
      (λ n → R.∣ R._-_ (shifted n) (partial m) ∣)
    absConvergent =
      R.∣ R._-_ limit (partial m) ∣ ,
      Seq.∣xₙ∣→∣x₀∣
        (R._-_ limit (partial m) , differenceConverges)

    boundEach : (n : Nat) →
      R._≤_
        (R.∣ R._-_ (shifted n) (partial m) ∣)
        (Uniform.inversePrecision k)
    boundEach n =
      RP.≤-respˡ-≃
        (RP.∣-∣-cong
          (sourceAtanPartialMinusIsTail point m (n + cutoff)))
        (sourceAtanUniformFiniteTail point inside k
          m (n + cutoff) mPast (NP.m≤n+m cutoff n))
  in
  Seq.xₙ≤y⇒limxₙ≤y boundEach absConvergent

-- A *single* index approximates BOTH literal Machin atan values.
originalMachinTwoPointUniformApproximation :
  (k : Nat) → .{{_ : NonZero k}} →
  R._≤_
    (R.∣
      R._-_
        (Seq.SeriesOf (Atan.atanSignedTerm Atan.bishopOneFifth)
          (sourceAtanUniformTailCutoff k))
        Atan.bishopAtanOneFifth
    ∣)
    (Uniform.inversePrecision k)
  ×
  R._≤_
    (R.∣
      R._-_
        (Seq.SeriesOf
          (Atan.atanSignedTerm Atan.bishopOneTwoHundredThirtyNinth)
          (sourceAtanUniformTailCutoff k))
        Atan.bishopAtanOneTwoHundredThirtyNinth
    ∣)
    (Uniform.inversePrecision k)
originalMachinTwoPointUniformApproximation k =
  RP.≤-respˡ-≃
    (RP.∣x-y∣≃∣y-x∣
      Atan.bishopAtanOneFifth
      (Seq.SeriesOf (Atan.atanSignedTerm Atan.bishopOneFifth)
        (sourceAtanUniformTailCutoff k)))
    (sourceAtanUniformLimitError
      Atan.bishopOneFifth Atan.bishopOneFifthInsideHalf
      k (sourceAtanUniformTailCutoff k) NP.≤-refl)
  ,
  RP.≤-respˡ-≃
    (RP.∣x-y∣≃∣y-x∣
      Atan.bishopAtanOneTwoHundredThirtyNinth
      (Seq.SeriesOf
        (Atan.atanSignedTerm Atan.bishopOneTwoHundredThirtyNinth)
        (sourceAtanUniformTailCutoff k)))
    (sourceAtanUniformLimitError
      Atan.bishopOneTwoHundredThirtyNinth
      Atan.bishopOneTwoHundredThirtyNinthInsideHalf
      k (sourceAtanUniformTailCutoff k) NP.≤-refl)
