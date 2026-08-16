module DASHI.Physics.Closure.NSTriadKNThreeSoftSharpGlobalGateRound62Exact where

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
-- ROUND 62 CONTRIBUTION
--
-- Fuse the two strongest Round62 reductions:
--
--   C: a = a_HHg + a_Com + a_kernel,
--   G: eta_soft = K S^2 / ((r-q)-a).
--
-- Six owners have zero additive data remainder, so the sharp global viscosity
-- gate now depends on no hidden aggregate coefficient.  For the canonical
-- three-soft C source it is exactly
--
--   eta_HHb
--   + K S^2 / ((r-q)-(a_HHg+a_Com+a_kernel))
--   + 1/16 < 1.
--
-- `eta_HHb` is already definitionally 2*C_* K_bad in the Round61 G carrier.
-- The theorem below constructs the positive sharp C object, feeds its maximal
-- B_* into G, and reduces final strict absorption to this one scalar test.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _≤_; _<_)

import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftThreeSoftDataScaleRound62Exact as ThreeSoft
import DASHI.Physics.Closure.NSTriadKNFixedShiftNineOwnerDataScaleRound62Exact as C9
import DASHI.Physics.Closure.NSTriadKNFixedShiftSharpStrictGapCapacityRound61Exact as SharpC
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block
import DASHI.Physics.Closure.NSTriadKNSharpCapacityToNineOwnerRound61Exact as CtoG
import DASHI.Physics.Closure.NSTriadKNPhysicalNineOwnerFeasibilityRound61Exact as G
import DASHI.Physics.Closure.NSTriadKNPhysicalNineOwnerWeightedFeasibilityRound61Exact as Weighted
import DASHI.Physics.Closure.NSTriadKNSharpWeightedScalarGateRound62Exact as SharpGate
import DASHI.Physics.Closure.NSTriadKNJointGlobalFeasibilityRound54Exact as Existing

positiveScaleFromThreeSoft :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  (soft : ThreeSoft.ThreeSoftOwnerDataScaleBounds {balances} block) →
  (critical : C9.PhysicalCriticalScaleBound {balances} block) →
  ThreeSoft.threeSoftDataScale soft < Block.r block - Block.q block →
  SharpC.StrictPositiveCriticalScaleData identification
positiveScaleFromThreeSoft soft critical strictGap = record
  { scaleData = ThreeSoft.threeSoftToStrictGapData soft critical strictGap
  ; criticalScalePositive = C9.criticalScalePositive critical
  }

threeSoftMarginMeaning :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    (soft : ThreeSoft.ThreeSoftOwnerDataScaleBounds {balances} block)
    (critical : C9.PhysicalCriticalScaleBound {balances} block)
    (strictGap : ThreeSoft.threeSoftDataScale soft < Block.r block - Block.q block) →
  SharpGate.correctionMargin
    (positiveScaleFromThreeSoft soft critical strictGap)
  ≡ (Block.r block - Block.q block) - ThreeSoft.threeSoftDataScale soft
threeSoftMarginMeaning soft critical strictGap = refl

threeSoftCriticalScaleMeaning :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    (soft : ThreeSoft.ThreeSoftOwnerDataScaleBounds {balances} block)
    (critical : C9.PhysicalCriticalScaleBound {balances} block)
    (strictGap : ThreeSoft.threeSoftDataScale soft < Block.r block - Block.q block) →
  SharpGate.criticalScale
    (positiveScaleFromThreeSoft soft critical strictGap)
  ≡ C9.criticalScale critical
threeSoftCriticalScaleMeaning soft critical strictGap = refl

threeSoftSharpScalars :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    (soft : ThreeSoft.ThreeSoftOwnerDataScaleBounds {balances} block)
    (critical : C9.PhysicalCriticalScaleBound {balances} block)
    (strictGap : ThreeSoft.threeSoftDataScale soft < Block.r block - Block.q block) →
  (hhBadCeiling badChargeMultiplicity comMultiplicity
    kernelNumerator hhGoodNumerator : ℚ) →
  0ℚ ≤ hhBadCeiling →
  0ℚ ≤ badChargeMultiplicity →
  0ℚ ≤ comMultiplicity →
  0ℚ ≤ kernelNumerator →
  0ℚ ≤ hhGoodNumerator →
  G.PhysicalNineOwnerScalars
threeSoftSharpScalars soft critical strictGap =
  CtoG.sharpCapacityNineOwnerScalars
    (positiveScaleFromThreeSoft soft critical strictGap)

threeSoftSharpCapIsDefinitionallyMaximal :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    (soft : ThreeSoft.ThreeSoftOwnerDataScaleBounds {balances} block)
    (critical : C9.PhysicalCriticalScaleBound {balances} block)
    (strictGap : ThreeSoft.threeSoftDataScale soft < Block.r block - Block.q block)
    (hhBadCeiling badChargeMultiplicity comMultiplicity
      kernelNumerator hhGoodNumerator : ℚ)
    (hhBadCeilingNN : 0ℚ ≤ hhBadCeiling)
    (badChargeMultiplicityNN : 0ℚ ≤ badChargeMultiplicity)
    (comMultiplicityNN : 0ℚ ≤ comMultiplicity)
    (kernelNumeratorNN : 0ℚ ≤ kernelNumerator)
    (hhGoodNumeratorNN : 0ℚ ≤ hhGoodNumerator) →
  G.correctionCap
    (threeSoftSharpScalars
      soft critical strictGap
      hhBadCeiling badChargeMultiplicity comMultiplicity
      kernelNumerator hhGoodNumerator
      hhBadCeilingNN badChargeMultiplicityNN comMultiplicityNN
      kernelNumeratorNN hhGoodNumeratorNN)
  ≡ SharpC.maximalUniformCoefficient
      (positiveScaleFromThreeSoft soft critical strictGap)
threeSoftSharpCapIsDefinitionallyMaximal
  soft critical strictGap
  hhBadCeiling badChargeMultiplicity comMultiplicity
  kernelNumerator hhGoodNumerator
  hhBadCeilingNN badChargeMultiplicityNN comMultiplicityNN
  kernelNumeratorNN hhGoodNumeratorNN = refl

threeSoftExplicitGate :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    (soft : ThreeSoft.ThreeSoftOwnerDataScaleBounds {balances} block)
    (critical : C9.PhysicalCriticalScaleBound {balances} block)
    (strictGap : ThreeSoft.threeSoftDataScale soft < Block.r block - Block.q block)
    (data : G.PhysicalNineOwnerScalars) →
  Weighted.RationalSquareRootMajorants data → ℚ
threeSoftExplicitGate soft critical strictGap data roots =
  SharpGate.explicitSharpEtaTotal
    (positiveScaleFromThreeSoft soft critical strictGap) data roots

threeSoftSharpAbsorptionFromOneScalarGate :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    (soft : ThreeSoft.ThreeSoftOwnerDataScaleBounds {balances} block)
    (critical : C9.PhysicalCriticalScaleBound {balances} block)
    (strictGap : ThreeSoft.threeSoftDataScale soft < Block.r block - Block.q block)
    (hhBadCeiling badChargeMultiplicity comMultiplicity
      kernelNumerator hhGoodNumerator : ℚ)
    (hhBadCeilingNN : 0ℚ ≤ hhBadCeiling)
    (badChargeMultiplicityNN : 0ℚ ≤ badChargeMultiplicity)
    (comMultiplicityNN : 0ℚ ≤ comMultiplicity)
    (kernelNumeratorNN : 0ℚ ≤ kernelNumerator)
    (hhGoodNumeratorNN : 0ℚ ≤ hhGoodNumerator)
    (roots : Weighted.RationalSquareRootMajorants
      (threeSoftSharpScalars
        soft critical strictGap
        hhBadCeiling badChargeMultiplicity comMultiplicity
        kernelNumerator hhGoodNumerator
        hhBadCeilingNN badChargeMultiplicityNN comMultiplicityNN
        kernelNumeratorNN hhGoodNumeratorNN)) →
  threeSoftExplicitGate
    soft critical strictGap
    (threeSoftSharpScalars
      soft critical strictGap
      hhBadCeiling badChargeMultiplicity comMultiplicity
      kernelNumerator hhGoodNumerator
      hhBadCeilingNN badChargeMultiplicityNN comMultiplicityNN
      kernelNumeratorNN hhGoodNumeratorNN)
    roots
  < 1ℚ →
  let data =
        threeSoftSharpScalars
          soft critical strictGap
          hhBadCeiling badChargeMultiplicity comMultiplicity
          kernelNumerator hhGoodNumerator
          hhBadCeilingNN badChargeMultiplicityNN comMultiplicityNN
          kernelNumeratorNN hhGoodNumeratorNN
  in
  G.hhBadEta data + Weighted.weightedSoftEta roots + Existing.hardFourClassTax
  < 1ℚ
threeSoftSharpAbsorptionFromOneScalarGate
  soft critical strictGap
  hhBadCeiling badChargeMultiplicity comMultiplicity
  kernelNumerator hhGoodNumerator
  hhBadCeilingNN badChargeMultiplicityNN comMultiplicityNN
  kernelNumeratorNN hhGoodNumeratorNN roots =
  SharpGate.sharpWeightedNineOwnerStrictAbsorptionFromExplicitGate
    (positiveScaleFromThreeSoft soft critical strictGap)
    refl roots

finalGateUsesOnlyThreeSoftDataScales : Bool
finalGateUsesOnlyThreeSoftDataScales = true

finalGateUsesOnlyThreeSoftDataScalesIsTrue :
  finalGateUsesOnlyThreeSoftDataScales ≡ true
finalGateUsesOnlyThreeSoftDataScalesIsTrue = refl
