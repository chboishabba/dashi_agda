module DASHI.Physics.Closure.NSTriadKNCriticalScaleNormalizedConsumerRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 63 C0 -> C1 CONSUMER WELD
--
-- `NSTriadKNCriticalScaleNormalizedBlockRound63Exact` constructs
--
--   Xi_n = X_n / (C r^n)
--
-- and proves X_n=(C r^n)Xi_n exactly on positive fixed blocks.  Therefore the
-- existing Round62 `PhysicalCriticalScaleBound` should not ask downstream code
-- to re-prove the scaled inequality.  A positive uniform bound Xi_n<=K plus
-- the already-required nonnegativity of the physical critical integral
-- constructs that record directly.
--
-- This is intentionally upstream of final B_* allocation/headroom.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block
import DASHI.Physics.Closure.NSTriadKNFixedShiftNineOwnerDataScaleRound62Exact as C9
import DASHI.Physics.Closure.NSTriadKNCriticalScaleNormalizedBlockRound63Exact as C0

normalizedUniformBoundToPhysicalCriticalScale :
  {balances : Nat → Nine.NineOwnerCriticalBalance} →
  (block : Block.RationalFixedBlockDecay) →
  (positiveScale : C0.PositiveCriticalBlockScale block) →
  (K : ℚ) →
  0ℚ < K →
  ((n : Nat) →
    0ℚ ≤ Owner.integralCritical (Nine.environment (balances n))) →
  ((n : Nat) →
    C0.normalizedCritical balances block positiveScale n ≤ K) →
  C9.PhysicalCriticalScaleBound {balances} block
normalizedUniformBoundToPhysicalCriticalScale
    {balances} block positiveScale K KPositive criticalNN normalizedBound = record
  { criticalScale = K
  ; criticalScalePositive = KPositive
  ; criticalIntegralNonnegative = criticalNN
  ; criticalScaleBound =
      C0.normalizedBoundImpliesCriticalScale
        balances block positiveScale K normalizedBound
  }

physicalCriticalScaleImpliesNormalizedUniformBound :
  {balances : Nat → Nine.NineOwnerCriticalBalance} →
  (block : Block.RationalFixedBlockDecay) →
  (positiveScale : C0.PositiveCriticalBlockScale block) →
  (physical : C9.PhysicalCriticalScaleBound {balances} block) →
  (n : Nat) →
  C0.normalizedCritical balances block positiveScale n
  ≤ C9.criticalScale physical
physicalCriticalScaleImpliesNormalizedUniformBound
    {balances} block positiveScale physical =
  C0.criticalScaleBoundImpliesNormalizedBound
    balances block positiveScale
    (C9.criticalScale physical)
    (C9.criticalScaleBound physical)

c1ReducedExactlyToScaleFreeUniformBound : Bool
c1ReducedExactlyToScaleFreeUniformBound = true

c1ReducedExactlyToScaleFreeUniformBoundIsTrue :
  c1ReducedExactlyToScaleFreeUniformBound ≡ true
c1ReducedExactlyToScaleFreeUniformBoundIsTrue = refl
