{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayOriginalL1Rational24CellBlockedMomentsExact where

------------------------------------------------------------------------
-- Exact normalized moments of the original finite 24-cell L=1
-- quadratic-Taylor Wilson effective RG law.
--
-- Source: YMClayOriginalL1Rational24CellEffectiveRGExact.
-- The source already certifies three relative weights and their
-- 6/16/2 multiplicities. This module computes the *normalized*
-- coarse moments for t = (Re (U0 U1))^2, and its variance.
-- All equations are Q normalization equalities (no postulates).
--
-- This is NOT an Agda derivation of the underlying 24^4 conditional
-- moments, an exponential Gibbs density, physical continuum RG,
-- or an infinite-volume Yang-Mills result.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
import DASHI.Physics.YangMills.YMClayOriginalL1Rational24CellEffectiveRGExact as RG

weightedFirst : ℚ
weightedFirst =
  (((+ 6 / 1) * RG.effectiveWeight RG.classZero * RG.classZero
     + (+ 16 / 1) * RG.effectiveWeight RG.classQuarter * RG.classQuarter)
     + (+ 2 / 1) * RG.effectiveWeight RG.classOne * RG.classOne)
    * (+ 1 / 24)

weightedSecond : ℚ
weightedSecond =
  (((+ 6 / 1) * RG.effectiveWeight RG.classZero *
       (RG.classZero * RG.classZero)
     + (+ 16 / 1) * RG.effectiveWeight RG.classQuarter *
       (RG.classQuarter * RG.classQuarter))
     + (+ 2 / 1) * RG.effectiveWeight RG.classOne *
       (RG.classOne * RG.classOne))
    * (+ 1 / 24)

firstNumeratorExact : weightedFirst ≡ (+ 634945 / 2654208)
firstNumeratorExact = refl

secondNumeratorExact : weightedSecond ≡ (+ 1273207 / 10616832)
secondNumeratorExact = refl

-- Explicit normalized values, using the already certified strictly
-- positive partition. Denominator / is the rational field operation;
-- no real-limit witness is hidden in the normalization.
meanT : ℚ
meanT = weightedFirst / RG.coarseTotal

secondT : ℚ
secondT = weightedSecond / RG.coarseTotal

varianceT : ℚ
varianceT = secondT - meanT * meanT

meanTExact : meanT ≡ (+ 634945 / 2533158)
meanTExact = refl

secondTExact : secondT ≡ (+ 1273207 / 10132632)
secondTExact = refl

varianceTExact : varianceT ≡ (+ 806306942803 / 12833778905928)
varianceTExact = refl

-- This is a genuinely nonzero normalized coarse variance, but
-- positivity as an Agda order theorem should be imported separately
-- if used by a future spectral or nontriviality consumer.
