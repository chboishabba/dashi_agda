module DASHI.Physics.Closure.NSTriadKNHHBadThresholdedOwnerCostRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- The companion Round-42 inverse-shell file computes the exact cost of
-- neutralizing the raw shell growth:
--
--   density_q * R_q = 2 C_q,
--
-- with C_q the scale-free one-derivative Schur coefficient.  The full HH-bad
-- owner also pays the directional bad-set threshold.  Round 40 already proved
-- this appears as delta^-1.  This file composes the two costs explicitly:
--
--   eta_HHb(actual) = delta^-1 * 2 C_q,
--
-- and under C_q <= C_bad,
--
--   eta_HHb <= delta^-1 * 2 C_bad.
--
-- This is the coefficient that belongs in the nine-owner optimizer.  It
-- corrects the tempting but incomplete practice of reading the pre-threshold
-- raw-ratio neutralization cost 2 C_bad as the final owner tax.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadInverseShellDensityFromSchurRound41Exact as Density
import DASHI.Physics.Closure.NSTriadKNHHBadInverseShellOwnerCostRound42Exact as Cost

actualThresholdedHHBadCost :
  ∀ {effectiveViscosity density shell} →
  Threshold.PositiveThreshold →
  Density.OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell → ℚ
actualThresholdedHHBadCost parameter certificate =
  Threshold.thresholdInverse parameter
    * (Sharp.two * Cost.scaleFreeCoefficient certificate)

boundedThresholdedHHBadCost :
  ∀ {effectiveViscosity density shell} →
  Threshold.PositiveThreshold →
  Density.OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell → ℚ
boundedThresholdedHHBadCost parameter certificate =
  Threshold.thresholdInverse parameter
    * (Sharp.two * Density.scaleFreeConstant certificate)

thresholdedDensityRawRatioExact :
  ∀ {effectiveViscosity density shell} →
  (parameter : Threshold.PositiveThreshold) →
  (certificate : Density.OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell) →
  Threshold.thresholdInverse parameter
    * (density * Sharp.rawHHBadRatio shell)
  ≡ actualThresholdedHHBadCost parameter certificate
thresholdedDensityRawRatioExact parameter certificate =
  cong (Threshold.thresholdInverse parameter *_)
    (Cost.inverseShellDensityTimesRawRatioExact certificate)

actualThresholdedCostBelowBoundedCost :
  ∀ {effectiveViscosity density shell} →
  (parameter : Threshold.PositiveThreshold) →
  (certificate : Density.OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell) →
  actualThresholdedHHBadCost parameter certificate
  ≤ boundedThresholdedHHBadCost parameter certificate
actualThresholdedCostBelowBoundedCost parameter certificate =
  let
    doubled = Cost.doubledScaleFreeCoefficientBelowDoubledBound certificate
    inverseNN = Threshold.thresholdInverseNonnegative parameter
  in
  let instance inverseNNI = nonNegative inverseNN
  in ℚP.*-monoˡ-≤-nonNeg
      (Threshold.thresholdInverse parameter) doubled

thresholdedDensityRawRatioBelowBoundedCost :
  ∀ {effectiveViscosity density shell} →
  (parameter : Threshold.PositiveThreshold) →
  (certificate : Density.OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell) →
  Threshold.thresholdInverse parameter
    * (density * Sharp.rawHHBadRatio shell)
  ≤ boundedThresholdedHHBadCost parameter certificate
thresholdedDensityRawRatioBelowBoundedCost parameter certificate =
  subst
    (λ lower → lower ≤ boundedThresholdedHHBadCost parameter certificate)
    (sym (thresholdedDensityRawRatioExact parameter certificate))
    (actualThresholdedCostBelowBoundedCost parameter certificate)

thresholdedHHBadCostFitsEta :
  ∀ {effectiveViscosity density shell} →
  (parameter : Threshold.PositiveThreshold) →
  (certificate : Density.OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell) →
  (eta : ℚ) →
  boundedThresholdedHHBadCost parameter certificate ≤ eta →
  Threshold.thresholdInverse parameter
    * (density * Sharp.rawHHBadRatio shell)
  ≤ eta
thresholdedHHBadCostFitsEta parameter certificate eta boundedCostBelowEta =
  ℚP.≤-trans
    (thresholdedDensityRawRatioBelowBoundedCost parameter certificate)
    boundedCostBelowEta

thresholdedHHBadOwnerCostClosed : Bool
thresholdedHHBadOwnerCostClosed = true

hhBadReserveMustUseInverseThresholdDoubledCoefficient : Bool
hhBadReserveMustUseInverseThresholdDoubledCoefficient = true

thresholdedHHBadOwnerCostClosedIsTrue :
  thresholdedHHBadOwnerCostClosed ≡ true
thresholdedHHBadOwnerCostClosedIsTrue = refl
