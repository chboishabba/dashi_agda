module DASHI.Physics.Closure.NSTriadKNFixedShiftStrictGapCapacityRound61Exact where

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
-- ROUND 61 CONTRIBUTION
--
-- C3 is not an independent physical obligation once C1 and C2 are known.
-- From
--
--   X_n <= K C r^n,    0 <= K,
--   A_n <= a C r^n,    a < r-q,
--
-- replace K by K+1 and define
--
--                 (r-q)-a
--       B_*  =  ------------- .
--                    K+1
--
-- Then B_*>0 and a+B_*(K+1)=r-q exactly.  This file therefore constructs the
-- existing Round60 ScaleMatchedFixedShiftCapacityData from C1+C2; Round60 then
-- supplies the uniform all-block product-capacity theorem.  No positive-B or
-- headroom witness is accepted independently here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; 1/_; positive; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; subst₂; sym; module ≡-Reasoning)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Round53
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftScaleMatchedCapacityRound60Exact as Scale
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

open ≡-Reasoning

record StrictGapBlockScaleData
    {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block) : Set where
  field
    criticalScale dataScale : ℚ
    criticalScaleNonnegative : 0ℚ ≤ criticalScale

    criticalIntegralNonnegative : ∀ n →
      0ℚ ≤ Owner.integralCritical (Nine.environment (balances n))

    criticalScaleBound : ∀ n →
      Owner.integralCritical (Nine.environment (balances n))
      ≤ criticalScale
        * Block.scaledTarget (Block.constant block) (Block.r block) n

    dataScaleBound : ∀ n →
      Round53.ownerAggregateDataRemainder (balances n)
      ≤ dataScale
        * Block.scaledTarget (Block.constant block) (Block.r block) n

    strictDataGap : dataScale < Block.r block - Block.q block

open StrictGapBlockScaleData public

raisedCriticalScale :
  ∀ {balances recursionData block identification} →
  StrictGapBlockScaleData
    {balances = balances} {recursionData = recursionData}
    {block = block} identification → ℚ
raisedCriticalScale data = criticalScale data + 1ℚ

raisedCriticalScalePositive :
  ∀ {balances recursionData block identification}
    (data : StrictGapBlockScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  0ℚ < raisedCriticalScale data
raisedCriticalScalePositive data =
  let
    onePositive : 0ℚ < 1ℚ
    onePositive = ℚP.positive⁻¹ 1ℚ
    shifted : 0ℚ + 0ℚ < criticalScale data + 1ℚ
    shifted = ℚP.+-mono-≤-< (criticalScaleNonnegative data) onePositive
  in
  subst
    (λ left → left < raisedCriticalScale data)
    (ℚP.+-identityˡ 0ℚ)
    shifted

criticalScaleBelowRaised :
  ∀ {balances recursionData block identification}
    (data : StrictGapBlockScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  criticalScale data ≤ raisedCriticalScale data
criticalScaleBelowRaised data =
  let
    shifted : criticalScale data + 0ℚ ≤ criticalScale data + 1ℚ
    shifted = ℚP.+-monoʳ-≤ (criticalScale data) ℚP.0≤1
  in
  subst
    (λ left → left ≤ raisedCriticalScale data)
    (ℚP.+-identityʳ (criticalScale data))
    shifted

correctionMargin :
  ∀ {balances recursionData block identification} →
  StrictGapBlockScaleData
    {balances = balances} {recursionData = recursionData}
    {block = block} identification → ℚ
correctionMargin {block = block} data =
  (Block.r block - Block.q block) - dataScale data

correctionMarginPositive :
  ∀ {balances recursionData block identification}
    (data : StrictGapBlockScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  0ℚ < correctionMargin data
correctionMarginPositive {block = block} data =
  let
    a = dataScale data
    gap = Block.r block - Block.q block
    shifted = ℚP.+-monoʳ-< (- a) (strictDataGap data)
    leftMeaning : a + (- a) ≡ 0ℚ
    leftMeaning = solve (a ∷ [])
    rightMeaning : gap + (- a) ≡ correctionMargin data
    rightMeaning = solve (gap ∷ a ∷ [])
  in
  subst₂ _<_ leftMeaning rightMeaning shifted

derivedUniformCoefficient :
  ∀ {balances recursionData block identification}
    (data : StrictGapBlockScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) → ℚ
derivedUniformCoefficient data =
  let
    scale = raisedCriticalScale data
    instance scaleNonzero = ℚ.>-nonZero (raisedCriticalScalePositive data)
  in
  correctionMargin data * ℚ.1/_ scale

derivedUniformCoefficientPositive :
  ∀ {balances recursionData block identification}
    (data : StrictGapBlockScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  0ℚ < derivedUniformCoefficient data
derivedUniformCoefficientPositive data =
  let
    margin = correctionMargin data
    scale = raisedCriticalScale data
    marginPositive = correctionMarginPositive data
    scalePositive = raisedCriticalScalePositive data
    instance
      marginPositiveI = positive marginPositive
      scalePositiveI = positive scalePositive
      scaleNonzero = ℚP.pos⇒nonZero scale
      inversePositiveI = ℚP.1/pos⇒pos scale
      productPositiveI = ℚP.pos*pos⇒pos margin (ℚ.1/_ scale)
  in
  ℚP.positive⁻¹ (derivedUniformCoefficient data)

derivedUniformCoefficientNonnegative :
  ∀ {balances recursionData block identification}
    (data : StrictGapBlockScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  0ℚ ≤ derivedUniformCoefficient data
derivedUniformCoefficientNonnegative data =
  ℚP.<⇒≤ (derivedUniformCoefficientPositive data)

raisedScaleTimesInverseIsOne :
  ∀ {balances recursionData block identification}
    (data : StrictGapBlockScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  let scale = raisedCriticalScale data
      instance scaleNonzero = ℚ.>-nonZero (raisedCriticalScalePositive data)
  in scale * ℚ.1/_ scale ≡ 1ℚ
raisedScaleTimesInverseIsOne data =
  let
    scale = raisedCriticalScale data
    instance scaleNonzero = ℚ.>-nonZero (raisedCriticalScalePositive data)
  in
  ℚP.*-inverseʳ scale

derivedCoefficientTimesRaisedScale :
  ∀ {balances recursionData block identification}
    (data : StrictGapBlockScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  derivedUniformCoefficient data * raisedCriticalScale data
  ≡ correctionMargin data
derivedCoefficientTimesRaisedScale data =
  let
    margin = correctionMargin data
    scale = raisedCriticalScale data
    instance scaleNonzero = ℚ.>-nonZero (raisedCriticalScalePositive data)
  in
  begin
    derivedUniformCoefficient data * scale
  ≡⟨ solve (margin ∷ ℚ.1/_ scale ∷ scale ∷ []) ⟩
    margin * (scale * ℚ.1/_ scale)
  ≡⟨ cong (margin *_) (raisedScaleTimesInverseIsOne data) ⟩
    margin * 1ℚ
  ≡⟨ ℚP.*-identityʳ margin ⟩
    margin
  ∎

derivedCoefficientHeadroomExact :
  ∀ {balances recursionData block identification}
    (data : StrictGapBlockScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  dataScale data
    + derivedUniformCoefficient data * raisedCriticalScale data
  ≡ Block.r block - Block.q block
derivedCoefficientHeadroomExact {block = block} data =
  begin
    dataScale data
      + derivedUniformCoefficient data * raisedCriticalScale data
  ≡⟨ cong (dataScale data +_) (derivedCoefficientTimesRaisedScale data) ⟩
    dataScale data + correctionMargin data
  ≡⟨ solve (dataScale data ∷ Block.r block ∷ Block.q block ∷ []) ⟩
    Block.r block - Block.q block
  ∎

raisedCriticalScaleBound :
  ∀ {balances recursionData block identification}
    (data : StrictGapBlockScaleData
      {balances = balances} {recursionData = recursionData}
      {block = block} identification) →
  ∀ n →
  Owner.integralCritical (Nine.environment (balances n))
  ≤ raisedCriticalScale data
      * Block.scaledTarget (Block.constant block) (Block.r block) n
raisedCriticalScaleBound {block = block} data n =
  let
    T = Block.scaledTarget (Block.constant block) (Block.r block) n
    targetNN : 0ℚ ≤ T
    targetNN =
      Block.scaledTargetNonnegative
        (Block.constant block) (Block.r block)
        (Block.constantNonnegative block) (Block.rNonnegative block) n
    scaleMonotone :
      criticalScale data * T ≤ raisedCriticalScale data * T
    scaleMonotone =
      let instance tNN = nonNegative targetNN
      in ℚP.*-monoʳ-≤-nonNeg T (criticalScaleBelowRaised data)
  in
  ℚP.≤-trans (criticalScaleBound data n) scaleMonotone

strictGapScaleMatchedCapacity :
  ∀ {balances recursionData block identification} →
  (data : StrictGapBlockScaleData
    {balances = balances} {recursionData = recursionData}
    {block = block} identification) →
  Scale.ScaleMatchedFixedShiftCapacityData
    {balances = balances} {recursionData = recursionData}
    {block = block} identification
strictGapScaleMatchedCapacity {block = block} data = record
  { uniformCoefficient = derivedUniformCoefficient data
  ; criticalScale = raisedCriticalScale data
  ; dataScale = dataScale data
  ; uniformCoefficientPositive = derivedUniformCoefficientPositive data
  ; uniformCoefficientNonnegative = derivedUniformCoefficientNonnegative data
  ; criticalIntegralNonnegative = criticalIntegralNonnegative data
  ; criticalScaleBound = raisedCriticalScaleBound data
  ; dataScaleBound = dataScaleBound data
  ; coefficientHeadroom =
      subst
        (λ lower → lower ≤ Block.r block - Block.q block)
        (sym (derivedCoefficientHeadroomExact data))
        ℚP.≤-refl
  }

c3DerivedFromC1C2 : Bool
c3DerivedFromC1C2 = true

c3DerivedFromC1C2IsTrue : c3DerivedFromC1C2 ≡ true
c3DerivedFromC1C2IsTrue = refl
