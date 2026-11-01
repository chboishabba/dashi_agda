module DASHI.Physics.Closure.ExactGate2ConditionalTheoremBase where

open import Level using (zero)
open import DASHI.Physics.Closure.OutsideSeamAbsorptionBase
  using (OutsideSeamAbsorptionModel)

----------------------------------------------------------------------
-- Exact Gate 2 conditional theorem kernel.
--
-- This is the algebraic composition of the two remaining exact Gate 2
-- lanes:
--
--   1. exact K_N(A) extremizer-aware transfer on the true carrier, and
--   2. exact outside-seam zero/absorption on the true carrier.
--
-- The outside-seam kernel closes the exact leakage ratio under the
-- quarter threshold.  This module packages the final monotone step from
-- that quarter threshold into the full Gate 2 unit threshold.

record ExactGate2ConditionalTheoremModel : Set₁ where
  constructor mkExactGate2ConditionalTheoremModel
  field
    outsideSeamModel : OutsideSeamAbsorptionModel

  open OutsideSeamAbsorptionModel outsideSeamModel public

  field
    unit-threshold : N

    quarter≤unit :
      one-quarter ≤ unit-threshold

  exactGate2ConditionalTheorem :
    total-leakage ≤ unit-threshold
  exactGate2ConditionalTheorem =
    trans≤
      total-leakage
      one-quarter
      unit-threshold
      total≤quarter-viaExactDirectional
      quarter≤unit

  exactGate2NoPollutionConditionalTheorem :
    (exact-kna-ratio + 0#) ≤ unit-threshold
  exactGate2NoPollutionConditionalTheorem =
    trans≤
      (exact-kna-ratio + 0#)
      one-quarter
      unit-threshold
      exactPlusZero≤quarter
      quarter≤unit

open ExactGate2ConditionalTheoremModel public
