module DASHI.Physics.Closure.NSTriadKNKernelZeroTwoSoftSharpGlobalGateRound62Exact where

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
-- ROUND 62 PREFERRED-GATE CONTRIBUTION
--
-- Combine the exact-independent-kernel-zero branch with the sharp fixed-shift
-- capacity and weighted Young allocator.  The additive data coefficient is
--
--   a = a_HHg + a_Com,
--
-- where the companion HH-good theorem identifies a_HHg with the smooth
-- periodic correction only.  The weighted root sum is
--
--   S = s_Com + s_HHg.
--
-- With K>0 and a<r-q, the maximal correction coefficient is
--
--   B_* = ((r-q)-a)/K,
--
-- and therefore the preferred final scalar gate is exactly
--
--   eta_HHb
--   + K (s_Com+s_HHg)^2 / ((r-q)-(a_HHg+a_Com))
--   + 1/16 < 1.
--
-- Round61 defines eta_HHb = 2 C_* K_bad.  No kernel term remains in either
-- numerator on this branch.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftKernelZeroTwoSoftDataScaleRound62Exact as TwoSoftC
import DASHI.Physics.Closure.NSTriadKNFixedShiftNineOwnerDataScaleRound62Exact as C9
import DASHI.Physics.Closure.NSTriadKNFixedShiftSharpStrictGapCapacityRound61Exact as SharpC
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block
import DASHI.Physics.Closure.NSTriadKNPhysicalNineOwnerFeasibilityRound61Exact as G
import DASHI.Physics.Closure.NSTriadKNPhysicalNineOwnerWeightedFeasibilityRound61Exact as Weighted
import DASHI.Physics.Closure.NSTriadKNKernelZeroTwoSoftWeightedGateRound62Exact as TwoSoftG
import DASHI.Physics.Closure.NSTriadKNSharpWeightedScalarGateRound62Exact as SharpGate
import DASHI.Physics.Closure.NSTriadKNJointGlobalFeasibilityRound54Exact as Existing

positiveScaleFromTwoSoft :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  (soft : TwoSoftC.KernelZeroTwoSoftDataScaleBounds {balances} block) →
  (critical : C9.PhysicalCriticalScaleBound {balances} block) →
  TwoSoftC.twoSoftDataScale soft < Block.r block - Block.q block →
  SharpC.StrictPositiveCriticalScaleData identification
positiveScaleFromTwoSoft soft critical strictGap = record
  { scaleData = TwoSoftC.twoSoftToStrictGapData soft critical strictGap
  ; criticalScalePositive = C9.criticalScalePositive critical
  }

twoSoftExplicitSharpEtaTotal :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  (soft : TwoSoftC.KernelZeroTwoSoftDataScaleBounds {balances} block) →
  (critical : C9.PhysicalCriticalScaleBound {balances} block) →
  (strictGap : TwoSoftC.twoSoftDataScale soft < Block.r block - Block.q block) →
  (data : G.PhysicalNineOwnerScalars) →
  TwoSoftG.KernelZeroTwoSoftRootMajorants data → ℚ
twoSoftExplicitSharpEtaTotal soft critical strictGap data roots =
  G.hhBadEta data
  + C9.criticalScale critical
      * TwoSoftG.twoRootSum roots * TwoSoftG.twoRootSum roots
      * SharpGate.correctionMarginInverse
          (positiveScaleFromTwoSoft soft critical strictGap)
  + Existing.oneSixteenth

twoSoftSharpEtaTotalMeaning :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    (soft : TwoSoftC.KernelZeroTwoSoftDataScaleBounds {balances} block)
    (critical : C9.PhysicalCriticalScaleBound {balances} block)
    (strictGap : TwoSoftC.twoSoftDataScale soft < Block.r block - Block.q block)
    {data : G.PhysicalNineOwnerScalars}
    (capIsSharp :
      G.correctionCap data
      ≡ SharpC.maximalUniformCoefficient
          (positiveScaleFromTwoSoft soft critical strictGap))
    (roots : TwoSoftG.KernelZeroTwoSoftRootMajorants data) →
  G.hhBadEta data
    + Weighted.weightedSoftEta (TwoSoftG.asThreeSlotRoots roots)
    + Existing.hardFourClassTax
  ≡ twoSoftExplicitSharpEtaTotal soft critical strictGap data roots
twoSoftSharpEtaTotalMeaning soft critical strictGap {data} capIsSharp roots =
  let
    positiveScale = positiveScaleFromTwoSoft soft critical strictGap
    oldS = Weighted.rootSum (TwoSoftG.asThreeSlotRoots roots)
    newS = TwoSoftG.twoRootSum roots
    inv = SharpGate.correctionMarginInverse positiveScale

    sharpMeaning :
      G.hhBadEta data
        + Weighted.weightedSoftEta (TwoSoftG.asThreeSlotRoots roots)
        + Existing.hardFourClassTax
      ≡ SharpGate.explicitSharpEtaTotal
          positiveScale data (TwoSoftG.asThreeSlotRoots roots)
    sharpMeaning =
      SharpGate.sharpWeightedEtaTotalMeaning
        positiveScale capIsSharp (TwoSoftG.asThreeSlotRoots roots)

    kMeaning : SharpGate.criticalScale positiveScale ≡ C9.criticalScale critical
    kMeaning = refl

    rootMeaning : oldS ≡ newS
    rootMeaning = TwoSoftG.threeSlotRootSumIsTwoRootSum roots

    moveK :
      SharpGate.explicitSharpEtaTotal
        positiveScale data (TwoSoftG.asThreeSlotRoots roots)
      ≡ G.hhBadEta data
        + C9.criticalScale critical * oldS * oldS * inv
        + Existing.oneSixteenth
    moveK =
      cong
        (λ selectedK →
          G.hhBadEta data + selectedK * oldS * oldS * inv
            + Existing.oneSixteenth)
        kMeaning

    moveS :
      G.hhBadEta data
        + C9.criticalScale critical * oldS * oldS * inv
        + Existing.oneSixteenth
      ≡ G.hhBadEta data
        + C9.criticalScale critical * newS * newS * inv
        + Existing.oneSixteenth
    moveS =
      cong
        (λ selectedS →
          G.hhBadEta data
            + C9.criticalScale critical * selectedS * selectedS * inv
            + Existing.oneSixteenth)
        rootMeaning
  in
  trans sharpMeaning (trans moveK moveS)

twoSoftSharpStrictAbsorptionFromExplicitGate :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    (soft : TwoSoftC.KernelZeroTwoSoftDataScaleBounds {balances} block)
    (critical : C9.PhysicalCriticalScaleBound {balances} block)
    (strictGap : TwoSoftC.twoSoftDataScale soft < Block.r block - Block.q block)
    {data : G.PhysicalNineOwnerScalars}
    (capIsSharp :
      G.correctionCap data
      ≡ SharpC.maximalUniformCoefficient
          (positiveScaleFromTwoSoft soft critical strictGap))
    (roots : TwoSoftG.KernelZeroTwoSoftRootMajorants data) →
  twoSoftExplicitSharpEtaTotal soft critical strictGap data roots < 1ℚ →
  G.hhBadEta data
    + Weighted.weightedSoftEta (TwoSoftG.asThreeSlotRoots roots)
    + Existing.hardFourClassTax
  < 1ℚ
twoSoftSharpStrictAbsorptionFromExplicitGate
    soft critical strictGap capIsSharp roots gate =
  subst
    (_< 1ℚ)
    (sym (twoSoftSharpEtaTotalMeaning
      soft critical strictGap capIsSharp roots))
    gate

preferredKernelZeroGateHasNoKernelCost : Bool
preferredKernelZeroGateHasNoKernelCost = true

preferredKernelZeroGateHasNoKernelCostIsTrue :
  preferredKernelZeroGateHasNoKernelCost ≡ true
preferredKernelZeroGateHasNoKernelCostIsTrue = refl
