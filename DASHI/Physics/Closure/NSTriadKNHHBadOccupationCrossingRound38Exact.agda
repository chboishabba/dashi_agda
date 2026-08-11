module DASHI.Physics.Closure.NSTriadKNHHBadOccupationCrossingRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Give the finite, division-free precursor of the proposed BV/layer-cake
-- control of the HH-bad region.  Two independent resources are retained:
--
--   * occupation: every bad sample pays at least a threshold theta;
--   * crossings: every good->bad entrance pays at least hysteresis delta.
--
-- Hence
--
--   repeatedCost theta badSamples <= integratedDefect,
--   repeatedCost delta crossings  <= positiveVariation.
--
-- This packages duration/occupation and transition count as a two-coordinate
-- object instead of conflating them.  The continuum coarea/BV theorem remains
-- a physical analytic step; no measure-theoretic identity is postulated here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNHHBadCrossingVariationCostRound37Exact as Crossing

record BadOccupationSample (threshold : ℚ) : Set where
  constructor bad-occupation-sample
  field
    realizedDefect : ℚ
    thresholdPaid : threshold ≤ realizedDefect

open BadOccupationSample public

sumOccupationDefect :
  ∀ {threshold} → List (BadOccupationSample threshold) → ℚ
sumOccupationDefect [] = 0ℚ
sumOccupationDefect (sample ∷ rest) =
  realizedDefect sample + sumOccupationDefect rest

occupationThresholdCostBound :
  ∀ {threshold}
    (samples : List (BadOccupationSample threshold)) →
  Crossing.repeatedCost threshold samples ≤ sumOccupationDefect samples
occupationThresholdCostBound [] = ℚP.≤-refl
occupationThresholdCostBound (sample ∷ rest) =
  ℚP.+-mono-≤
    (thresholdPaid sample)
    (occupationThresholdCostBound rest)

record IntegratedDefectCharge
    {threshold : ℚ}
    (samples : List (BadOccupationSample threshold)) : Set where
  constructor integrated-defect-charge
  field
    integratedDefect : ℚ
    occupationDefectBelowIntegral :
      sumOccupationDefect samples ≤ integratedDefect

open IntegratedDefectCharge public

occupationCostBelowIntegratedDefect :
  ∀ {threshold samples} →
  (charge : IntegratedDefectCharge {threshold} samples) →
  Crossing.repeatedCost threshold samples ≤ integratedDefect charge
occupationCostBelowIntegratedDefect {samples = samples} charge =
  ℚP.≤-trans
    (occupationThresholdCostBound samples)
    (occupationDefectBelowIntegral charge)

record HHBadTwoCoordinateBudget : Set where
  constructor hhbad-two-coordinate-budget
  field
    badThreshold : ℚ
    badSamples : List (BadOccupationSample badThreshold)
    occupationCharge : IntegratedDefectCharge badSamples

    hysteresisJump : ℚ
    crossings : List (Crossing.BadCrossing hysteresisJump)
    variationCharge : Crossing.PositiveVariationCharge crossings

open HHBadTwoCoordinateBudget public

record HHBadTwoCoordinateControl
    (budget : HHBadTwoCoordinateBudget) : Set where
  constructor hhbad-two-coordinate-control
  field
    occupationControlled :
      Crossing.repeatedCost
        (badThreshold budget) (badSamples budget)
      ≤ integratedDefect (occupationCharge budget)
    crossingCountControlled :
      Crossing.repeatedCost
        (hysteresisJump budget) (crossings budget)
      ≤ Crossing.positiveVariation (variationCharge budget)

open HHBadTwoCoordinateControl public

twoCoordinateBadRegionControl :
  (budget : HHBadTwoCoordinateBudget) →
  HHBadTwoCoordinateControl budget
twoCoordinateBadRegionControl budget =
  hhbad-two-coordinate-control
    (occupationCostBelowIntegratedDefect (occupationCharge budget))
    (Crossing.hystereticCrossingCostBound (variationCharge budget))

hhBadOccupationCrossingFiniteControlClosed : Bool
hhBadOccupationCrossingFiniteControlClosed = true

physicalHHBadIntegratedDefectBoundConstructed : Bool
physicalHHBadIntegratedDefectBoundConstructed = false

physicalHHBadPositiveVariationBoundConstructed : Bool
physicalHHBadPositiveVariationBoundConstructed = false

hhBadOccupationCrossingFiniteControlClosedIsTrue :
  hhBadOccupationCrossingFiniteControlClosed ≡ true
hhBadOccupationCrossingFiniteControlClosedIsTrue = refl
