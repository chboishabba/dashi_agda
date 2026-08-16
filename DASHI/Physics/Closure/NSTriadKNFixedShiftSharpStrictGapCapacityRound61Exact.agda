module DASHI.Physics.Closure.NSTriadKNFixedShiftSharpStrictGapCapacityRound61Exact where

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
-- ROUND 61 SHARP C3 BRANCH
--
-- The zero-safe Round61 construction replaces K by K+1.  That is sufficient
-- to prove existence of a positive correction coefficient from C1+C2, but it
-- needlessly spends critical-resource headroom when the physical scale K is
-- already strictly positive.
--
-- For K>0 the exact maximal coefficient allowed by the scale-matched budget is
--
--              (r-q)-a
--       Bmax = --------- .
--                  K
--
-- Since C2 gives (r-q)-a>0, Bmax>0 and
--
--       a + Bmax K = r-q
--
-- exactly.  This module constructs the existing Round60 capacity with the
-- ORIGINAL K, so the later G feasibility test receives the largest correction
-- cap justified by these two scale bounds.  No optimization variable remains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _<_; 1/_; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; module ≡-Reasoning)

import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftScaleMatchedCapacityRound60Exact as Scale
import DASHI.Physics.Closure.NSTriadKNFixedShiftStrictGapCapacityRound61Exact as Base
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

open ≡-Reasoning

record StrictPositiveCriticalScaleData
    {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block) : Set where
  field
    scaleData : Base.StrictGapBlockScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification
    criticalScalePositive : 0ℚ < Base.criticalScale scaleData

open StrictPositiveCriticalScaleData public

maximalUniformCoefficient :
  ∀ {balances recursionData block identification} →
  StrictPositiveCriticalScaleData
    {balances = balances} {recursionData = recursionData}
    {block = block} identification → ℚ
maximalUniformCoefficient positiveData =
  let
    data = scaleData positiveData
    K = Base.criticalScale data
    instance kNonzero = ℚ.>-nonZero (criticalScalePositive positiveData)
  in
  Base.correctionMargin data * ℚ.1/_ K

maximalUniformCoefficientPositive :
  ∀ {balances recursionData block identification}
    (positiveData : StrictPositiveCriticalScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  0ℚ < maximalUniformCoefficient positiveData
maximalUniformCoefficientPositive positiveData =
  let
    data = scaleData positiveData
    margin = Base.correctionMargin data
    K = Base.criticalScale data
    marginPositive = Base.correctionMarginPositive data
    kPositive = criticalScalePositive positiveData
    instance
      marginPositiveI = positive marginPositive
      kPositiveI = positive kPositive
      kNonzero = ℚP.pos⇒nonZero K
      inversePositiveI = ℚP.1/pos⇒pos K
      productPositiveI = ℚP.pos*pos⇒pos margin (ℚ.1/_ K)
  in
  ℚP.positive⁻¹ (maximalUniformCoefficient positiveData)

maximalUniformCoefficientNonnegative :
  ∀ {balances recursionData block identification}
    (positiveData : StrictPositiveCriticalScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  0ℚ ≤ maximalUniformCoefficient positiveData
maximalUniformCoefficientNonnegative positiveData =
  ℚP.<⇒≤ (maximalUniformCoefficientPositive positiveData)

criticalScaleTimesInverseIsOne :
  ∀ {balances recursionData block identification}
    (positiveData : StrictPositiveCriticalScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  let data = scaleData positiveData
      K = Base.criticalScale data
      instance kNonzero = ℚ.>-nonZero (criticalScalePositive positiveData)
  in K * ℚ.1/_ K ≡ 1ℚ
criticalScaleTimesInverseIsOne positiveData =
  let
    data = scaleData positiveData
    K = Base.criticalScale data
    instance kNonzero = ℚ.>-nonZero (criticalScalePositive positiveData)
  in
  ℚP.*-inverseʳ K

maximalCoefficientTimesCriticalScale :
  ∀ {balances recursionData block identification}
    (positiveData : StrictPositiveCriticalScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  maximalUniformCoefficient positiveData
    * Base.criticalScale (scaleData positiveData)
  ≡ Base.correctionMargin (scaleData positiveData)
maximalCoefficientTimesCriticalScale positiveData =
  let
    data = scaleData positiveData
    margin = Base.correctionMargin data
    K = Base.criticalScale data
    instance kNonzero = ℚ.>-nonZero (criticalScalePositive positiveData)
  in
  begin
    maximalUniformCoefficient positiveData * K
  ≡⟨ solve (margin ∷ ℚ.1/_ K ∷ K ∷ []) ⟩
    margin * (K * ℚ.1/_ K)
  ≡⟨ cong (margin *_) (criticalScaleTimesInverseIsOne positiveData) ⟩
    margin * 1
  ≡⟨ ℚP.*-identityʳ margin ⟩
    margin
  ∎

maximalCoefficientHeadroomExact :
  ∀ {balances recursionData block identification}
    (positiveData : StrictPositiveCriticalScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  let data = scaleData positiveData
  in
  Base.dataScale data
    + maximalUniformCoefficient positiveData * Base.criticalScale data
  ≡ Block.r block - Block.q block
maximalCoefficientHeadroomExact {block = block} positiveData =
  let data = scaleData positiveData
  in
  begin
    Base.dataScale data
      + maximalUniformCoefficient positiveData * Base.criticalScale data
  ≡⟨ cong (Base.dataScale data +_)
        (maximalCoefficientTimesCriticalScale positiveData) ⟩
    Base.dataScale data + Base.correctionMargin data
  ≡⟨ solve (Base.dataScale data ∷ Block.r block ∷ Block.q block ∷ []) ⟩
    Block.r block - Block.q block
  ∎

sharpStrictGapScaleMatchedCapacity :
  ∀ {balances recursionData block identification} →
  (positiveData : StrictPositiveCriticalScaleData
    {balances = balances} {recursionData = recursionData}
    {block = block} identification) →
  Scale.ScaleMatchedFixedShiftCapacityData
    {balances = balances} {recursionData = recursionData}
    {block = block} identification
sharpStrictGapScaleMatchedCapacity {block = block} positiveData =
  let data = scaleData positiveData
  in record
    { uniformCoefficient = maximalUniformCoefficient positiveData
    ; criticalScale = Base.criticalScale data
    ; dataScale = Base.dataScale data
    ; uniformCoefficientPositive =
        maximalUniformCoefficientPositive positiveData
    ; uniformCoefficientNonnegative =
        maximalUniformCoefficientNonnegative positiveData
    ; criticalIntegralNonnegative = Base.criticalIntegralNonnegative data
    ; criticalScaleBound = Base.criticalScaleBound data
    ; dataScaleBound = Base.dataScaleBound data
    ; coefficientHeadroom =
        subst
          (λ lower → lower ≤ Block.r block - Block.q block)
          (sym (maximalCoefficientHeadroomExact positiveData))
          ℚP.≤-refl
    }

sharpC3UsesOriginalPositiveCriticalScale : Bool
sharpC3UsesOriginalPositiveCriticalScale = true

sharpC3UsesOriginalPositiveCriticalScaleIsTrue :
  sharpC3UsesOriginalPositiveCriticalScale ≡ true
sharpC3UsesOriginalPositiveCriticalScaleIsTrue = refl
