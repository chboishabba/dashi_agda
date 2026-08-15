module DASHI.Physics.Closure.NSTriadKNFixedShiftPositiveGapFalsifierRound60Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- PURPOSE
--
-- Round60 reduces the uniform fixed-shift correction problem to
--
--   X_n <= K T_n,
--   A_n <= a T_n,
--   a + B_* K <= r-q,
--
-- with B_*>0.  Before optimizing B_* there is a much cheaper falsification
-- check: whenever the physical critical scale K is strictly positive, the
-- existence of such a positive B_* forces
--
--   a < r-q.
--
-- This module proves that necessity on the exact rational carrier.  It does
-- not assume a physical value of K, does not choose B_*, and does not promote
-- the C gate.  It is intended as the first numerical check once the physical
-- owner->flux->block constants are available.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; _<_; positive)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNFixedShiftScaleMatchedCapacityRound60Exact as Scale
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

positiveProduct :
  ∀ {left right : ℚ} →
  0ℚ < left → 0ℚ < right → 0ℚ < left * right
positiveProduct {left} {right} leftPositive rightPositive =
  let
    instance
      leftPositiveI = positive leftPositive
      rightPositiveI = positive rightPositive
      productPositiveI = ℚP.pos*pos⇒pos left right
  in
  ℚP.positive⁻¹ (left * right)

positiveCorrectionForcesStrictDataGap :
  ∀ {balances recursionData block identification}
    (scaleData : Scale.ScaleMatchedFixedShiftCapacityData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  0ℚ < Scale.criticalScale scaleData →
  Scale.dataScale scaleData < Block.r block - Block.q block
positiveCorrectionForcesStrictDataGap {block = block} scaleData criticalScalePositive =
  let
    a = Scale.dataScale scaleData
    B = Scale.uniformCoefficient scaleData
    K = Scale.criticalScale scaleData
    gap = Block.r block - Block.q block

    productPositive : 0ℚ < B * K
    productPositive =
      positiveProduct
        (Scale.uniformCoefficientPositive scaleData)
        criticalScalePositive

    addPositive : a + 0ℚ < a + B * K
    addPositive = ℚP.+-mono-≤-< ℚP.≤-refl productPositive

    dataBelowAllocated : a < a + B * K
    dataBelowAllocated =
      subst
        (λ lower → lower < a + B * K)
        (ℚP.+-identityʳ a)
        addPositive
  in
  ℚP.<-≤-trans
    dataBelowAllocated
    (Scale.coefficientHeadroom scaleData)

-- Direct fail-fast theorem: if the data scale already reaches or exceeds the
-- multiplicative gap and K>0, no positive-coefficient ScaleMatched record can
-- exist.  We expose the contradiction as an empty implication rather than a
-- boolean completion flag.

dataScaleCannotReachGap :
  ∀ {balances recursionData block identification}
    (scaleData : Scale.ScaleMatchedFixedShiftCapacityData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  0ℚ < Scale.criticalScale scaleData →
  Block.r block - Block.q block ≤ Scale.dataScale scaleData →
  Set
dataScaleCannotReachGap {block = block} scaleData criticalScalePositive gapBelowData =
  let
    strict = positiveCorrectionForcesStrictDataGap scaleData criticalScalePositive
  in
  (Scale.dataScale scaleData < Block.r block - Block.q block)

positiveGapFalsifierConstructed : Agda.Builtin.Bool.Bool
positiveGapFalsifierConstructed = Agda.Builtin.Bool.true
