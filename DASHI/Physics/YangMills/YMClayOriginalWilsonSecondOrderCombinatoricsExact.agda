{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayOriginalWilsonSecondOrderCombinatoricsExact where

-- Original 4D periodic SU2 Wilson high-temperature combinatorial
-- coefficient calculation. This module is deliberately NUMERIC and
-- does NOT assert the still-open Haar integral equals its moment
-- functional or a physical continuum gap.
--
-- Source owners: YMClayNativePositiveBondEnumerationVectorExact
-- and native six-positive-plane Wilson action (rather than the
-- incorrect 16-ordered-axis action).
-- At side 4: 1024 original positive links, 1536 plaquettes.
-- Conditional on independent normalized one-link moments:
-- H(t_p)=0, H(t_p^2)=1/4 and H(t_p t_q)=0 (p != q),
-- Z(beta)=1-P beta+(P^2/2+P/8) beta^2+O(beta^3).
-- The geometric distinct-support verification is in the exact
-- companion checker, not silently assumed as this Agda theorem.
-- Attribution: Wilson/Balaban and original DASHI finite 4-torus owners.

open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact
  as OriginalBonds

positivePlaneCount : Nat
positivePlaneCount = 6

fourVolume : Nat → Nat
fourVolume L = (L * L) * (L * L)

originalSixPlaquetteCount : Nat → Nat
originalSixPlaquetteCount L = positivePlaneCount * fourVolume L

originalSideFourPositiveBonds :
  OriginalBonds.originalPositiveBondCount 4 ≡ 1024
originalSideFourPositiveBonds = OriginalBonds.originalSideFourCountIs1024

originalSideFourSixPlaquettes :
  originalSixPlaquetteCount 4 ≡ 1536
originalSideFourSixPlaquettes = refl

-- 8 times the coefficient of beta^2: 4P^2 + P.
-- This avoids any rational-number coercion in the safe Nat ledger.
originalWilsonSecondCoefficientTimesEight : Nat → Nat
originalWilsonSecondCoefficientTimesEight L =
  (4 * (originalSixPlaquetteCount L *
        originalSixPlaquetteCount L))
  + originalSixPlaquetteCount L

originalSideFourSecondCoefficientTimesEight :
  originalWilsonSecondCoefficientTimesEight 4 ≡ 9438720
originalSideFourSecondCoefficientTimesEight = refl

originalSideFourSecondCoefficientInteger :
  originalWilsonSecondCoefficientTimesEight 4
  ≡ 8 * 1179840
originalSideFourSecondCoefficientInteger = refl

-- First coefficient is negative, so it is recorded as a natural
-- magnitude; do not encode a fake negative Nat.
originalSideFourFirstCoefficientMagnitude :
  originalSixPlaquetteCount 4 ≡ 1536
originalSideFourFirstCoefficientMagnitude = refl
