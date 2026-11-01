module DASHI.Analysis.BishopMachinQuantitativeOmittedTailExact where

------------------------------------------------------------------------
-- K04b2: TRUE BISHOP REAL-ORDER FIRST-OMITTED REMAINDER CERTIFICATES.
-- Historical alternating series / Machin (1706), Bishop & Bridges
-- (1985), DOI 10.1007/978-3-642-61667-9; Murray (2022),
-- arXiv:2205.08354.
--
-- This is an *instantiation*, not another alternating-series theorem:
-- original BishopArctanHalfBallInterlacingExact already constructs
-- the actual arctan lower/upper partials and first omitted terms.
-- original BalabanBishopAlternatingBracketFromMonotoneLimitsExact
-- already proves order closure for the represented limit.
-- original BalabanBishopSetoidAlternatingFirstOmittedExact proves the
-- universally valid signed tail inequalities over Bishop real order.
-- The remaining K04b2 arithmetic is first omitted magnitude <=
-- 1/((2n+1)x^(2n+1)) and the combined 16/4 quantitative envelope.
-- New source written; Agda kernel receipt pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Real as Bishop
import RealProperties as RP
import Sequence as Series
import Data.Rational.Unnormalised as Q using (ℚᵘ; _*_)

import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Rational
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete

import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopArctanHalfBallInterlacingExact as Atan
import DASHI.Foundations.BishopMachinPiRationalWindowExact as Window
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Brackets
import DASHI.Physics.YangMills.BalabanBishopSetoidAlternatingFirstOmittedExact as Tail

-- A reusable specialization on an ACTUAL positive Bishop arctan
-- source, without introducing any analytic target as a record field.
actualArctanTail :
  ∀ {value : Bishop.ℝ} →
  (point : Atan.PositiveHalfBallPoint value) →
  Tail.SetoidSignedFirstOmittedTail
    Tail.bishopSetoidOrderedDifferenceKernel
actualArctanTail point =
  Tail.bishopAlternatingBracketsGiveFirstOmittedTail
    (Brackets.bishopAlternatingBracketsFromInterlacing
      (Atan.atanInterlacing point))

-- Even partial prefixes use their first omitted positive term.
actualArctanEvenRemainderBound :
  ∀ {value : Bishop.ℝ}
  (point : Atan.PositiveHalfBallPoint value) →
  ∀ k →
  Bishop._≤_
    (Bishop._-_
      (Machin.bishopAtanHalfBall value (Atan.insideHalf point))
      (Series.SeriesOf (Machin.atanSignedTerm value)
        (Alternating.double k)))
    (Machin.atanMagnitudeTerm value (Alternating.double k))
actualArctanEvenRemainderBound point k =
  Tail.lowerTailBelowFirstOmitted (actualArctanTail point) k

-- Odd partial prefixes use their first omitted negative term.
actualArctanOddRemainderBound :
  ∀ {value : Bishop.ℝ}
  (point : Atan.PositiveHalfBallPoint value) →
  ∀ k →
  Bishop._≤_
    (Bishop._-_
      (Series.SeriesOf (Machin.atanSignedTerm value)
        (suc (Alternating.double k)))
      (Machin.bishopAtanHalfBall value (Atan.insideHalf point)))
    (Machin.atanMagnitudeTerm value (suc (Alternating.double k)))
actualArctanOddRemainderBound point k =
  Tail.upperTailBelowFirstOmitted (actualArctanTail point) k

-- The original two Machin arguments instantiate these true
-- Bishop-order theorems. The numeric 5/239 quotient reduction
-- and combined signed 16/4 envelope are independent next lemmas.
fifthEvenRemainderBound : ∀ k →
  Bishop._≤_
    (Bishop._-_
      Machin.bishopAtanOneFifth
      (Series.SeriesOf (Machin.atanSignedTerm Machin.bishopOneFifth)
        (Alternating.double k)))
    (Machin.atanMagnitudeTerm Machin.bishopOneFifth
      (Alternating.double k))
fifthEvenRemainderBound =
  actualArctanEvenRemainderBound Window.oneFifthPoint

fifthOddRemainderBound : ∀ k →
  Bishop._≤_
    (Bishop._-_
      (Series.SeriesOf (Machin.atanSignedTerm Machin.bishopOneFifth)
        (suc (Alternating.double k)))
      Machin.bishopAtanOneFifth)
    (Machin.atanMagnitudeTerm Machin.bishopOneFifth
      (suc (Alternating.double k)))
fifthOddRemainderBound =
  actualArctanOddRemainderBound Window.oneFifthPoint

twoHundredThirtyNineEvenRemainderBound : ∀ k →
  Bishop._≤_
    (Bishop._-_
      Machin.bishopAtanOneTwoHundredThirtyNinth
      (Series.SeriesOf
        (Machin.atanSignedTerm Machin.bishopOneTwoHundredThirtyNinth)
        (Alternating.double k)))
    (Machin.atanMagnitudeTerm Machin.bishopOneTwoHundredThirtyNinth
      (Alternating.double k))
twoHundredThirtyNineEvenRemainderBound =
  actualArctanEvenRemainderBound Window.oneTwoHundredThirtyNinthPoint

twoHundredThirtyNineOddRemainderBound : ∀ k →
  Bishop._≤_
    (Bishop._-_
      (Series.SeriesOf
        (Machin.atanSignedTerm Machin.bishopOneTwoHundredThirtyNinth)
        (suc (Alternating.double k)))
      Machin.bishopAtanOneTwoHundredThirtyNinth)
    (Machin.atanMagnitudeTerm Machin.bishopOneTwoHundredThirtyNinth
      (suc (Alternating.double k)))
twoHundredThirtyNineOddRemainderBound =
  actualArctanOddRemainderBound Window.oneTwoHundredThirtyNinthPoint

------------------------------------------------------------------------
-- K04b2: ACTUAL FIRST-OMITTED BISHOP MAGNITUDE = RATIONAL SOURCE
-- (under the ORIGINAL certified nonnegative Machin arguments).
--
-- This uses the earlier all-index qPowEmbeds from K04a and the
-- pre-existing source's pointwise power-nonnegativity theorem. The
-- absolute value is not silently dropped for arbitrary signed x.
------------------------------------------------------------------------

atanMagnitudeIsEmbeddedRational :
  (x : Q.ℚᵘ) →
  (nonnegative : Bishop.NonNegative (Bishop._⋆ x)) →
  ∀ k →
  Bishop._≃_
    (Machin.atanMagnitudeTerm (Bishop._⋆ x) k)
    (Bishop._⋆
      (Machin.inverseOddRational k Q.*
        Rational.qPow x (Estimates.oddExponent k)))
atanMagnitudeIsEmbeddedRational x nonnegative k =
  RP.≃-trans
    (RP.*-congˡ
      (RP.nonNegx⇒∣x∣≃x
        (Concrete.powNonnegative nonnegative
          (Estimates.oddExponent k))))
    (RP.≃-symm
      (RP.≃-trans
        (RP.⋆-distrib-*
          (Machin.inverseOddRational k)
          (Rational.qPow x (Estimates.oddExponent k)))
        (RP.*-cong RP.≃-refl
          (Rational.qPowEmbeds x (Estimates.oddExponent k)))))

fifthFirstOmittedEqualsEmbeddedRational :
  ∀ k →
  Bishop._≃_
    (Machin.atanMagnitudeTerm Machin.bishopOneFifth k)
    (Bishop._⋆
      (Machin.inverseOddRational k Q.*
        Rational.qPow Machin.oneFifth (Estimates.oddExponent k)))
fifthFirstOmittedEqualsEmbeddedRational =
  atanMagnitudeIsEmbeddedRational
    Machin.oneFifth Machin.oneFifthNonnegative

twoHundredThirtyNineFirstOmittedEqualsEmbeddedRational :
  ∀ k →
  Bishop._≃_
    (Machin.atanMagnitudeTerm
      Machin.bishopOneTwoHundredThirtyNinth k)
    (Bishop._⋆
      (Machin.inverseOddRational k Q.*
        Rational.qPow Machin.oneTwoHundredThirtyNinth
          (Estimates.oddExponent k)))
twoHundredThirtyNineFirstOmittedEqualsEmbeddedRational =
  atanMagnitudeIsEmbeddedRational
    Machin.oneTwoHundredThirtyNinth
    Machin.oneTwoHundredThirtyNinthNonnegative
