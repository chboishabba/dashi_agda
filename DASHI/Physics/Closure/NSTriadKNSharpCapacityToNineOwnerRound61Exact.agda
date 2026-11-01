module DASHI.Physics.Closure.NSTriadKNSharpCapacityToNineOwnerRound61Exact where

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
-- Do not let the final G feasibility test choose an arbitrary correction cap
-- after C has already determined the largest one justified by the physical
-- scale bounds.  For strictly positive critical scale K, Round61 C proves
--
--              (r-q)-a
--       Bmax = --------- > 0.
--                  K
--
-- This module feeds THAT exact Bmax into the G scalar carrier.  The remaining
-- inputs are only the physical HH-bad ceiling/multiplicity, the Com lifting
-- multiplicity, and the kernel/HH-good Young numerators with their sign facts.
--
-- Therefore every equal-third or weighted Round61 G test constructed from this
-- bridge uses the sharp C1/C2 correction capacity by definition, not a weaker
-- manually supplied cap.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftSharpStrictGapCapacityRound61Exact as C
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block
import DASHI.Physics.Closure.NSTriadKNPhysicalNineOwnerFeasibilityRound61Exact as G

sharpCapacityNineOwnerScalars :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  (positiveScale : C.StrictPositiveCriticalScaleData identification) →
  (hhBadCeiling badChargeMultiplicity comMultiplicity
    kernelNumerator hhGoodNumerator : ℚ) →
  0ℚ ≤ hhBadCeiling →
  0ℚ ≤ badChargeMultiplicity →
  0ℚ ≤ comMultiplicity →
  0ℚ ≤ kernelNumerator →
  0ℚ ≤ hhGoodNumerator →
  G.PhysicalNineOwnerScalars
sharpCapacityNineOwnerScalars
    positiveScale
    hhBadCeiling badChargeMultiplicity comMultiplicity
    kernelNumerator hhGoodNumerator
    hhBadCeilingNN badChargeMultiplicityNN comMultiplicityNN
    kernelNumeratorNN hhGoodNumeratorNN = record
  { hhBadCeiling = hhBadCeiling
  ; badChargeMultiplicity = badChargeMultiplicity
  ; correctionCap = C.maximalUniformCoefficient positiveScale
  ; comMultiplicity = comMultiplicity
  ; kernelNumerator = kernelNumerator
  ; hhGoodNumerator = hhGoodNumerator
  ; hhBadCeilingNonnegative = hhBadCeilingNN
  ; badChargeMultiplicityNonnegative = badChargeMultiplicityNN
  ; correctionCapPositive = C.maximalUniformCoefficientPositive positiveScale
  ; comMultiplicityNonnegative = comMultiplicityNN
  ; kernelNumeratorNonnegative = kernelNumeratorNN
  ; hhGoodNumeratorNonnegative = hhGoodNumeratorNN
  }

sharpCapacityIsUsedDefinitionally :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    (positiveScale : C.StrictPositiveCriticalScaleData identification)
    (hhBadCeiling badChargeMultiplicity comMultiplicity
      kernelNumerator hhGoodNumerator : ℚ)
    (hhBadCeilingNN : 0ℚ ≤ hhBadCeiling)
    (badChargeMultiplicityNN : 0ℚ ≤ badChargeMultiplicity)
    (comMultiplicityNN : 0ℚ ≤ comMultiplicity)
    (kernelNumeratorNN : 0ℚ ≤ kernelNumerator)
    (hhGoodNumeratorNN : 0ℚ ≤ hhGoodNumerator) →
  G.correctionCap
    (sharpCapacityNineOwnerScalars
      positiveScale
      hhBadCeiling badChargeMultiplicity comMultiplicity
      kernelNumerator hhGoodNumerator
      hhBadCeilingNN badChargeMultiplicityNN comMultiplicityNN
      kernelNumeratorNN hhGoodNumeratorNN)
  ≡ C.maximalUniformCoefficient positiveScale
sharpCapacityIsUsedDefinitionally
  positiveScale
  hhBadCeiling badChargeMultiplicity comMultiplicity
  kernelNumerator hhGoodNumerator
  hhBadCeilingNN badChargeMultiplicityNN comMultiplicityNN
  kernelNumeratorNN hhGoodNumeratorNN = refl

sharpCFeedsGWithoutManualCorrectionCap : Bool
sharpCFeedsGWithoutManualCorrectionCap = true

sharpCFeedsGWithoutManualCorrectionCapIsTrue :
  sharpCFeedsGWithoutManualCorrectionCap ≡ true
sharpCFeedsGWithoutManualCorrectionCapIsTrue = refl
