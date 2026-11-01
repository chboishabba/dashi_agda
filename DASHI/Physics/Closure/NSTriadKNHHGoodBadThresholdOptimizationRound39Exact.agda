module DASHI.Physics.Closure.NSTriadKNHHGoodBadThresholdOptimizationRound39Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- The HH good/bad threshold is not an external tuning knob.  Increasing it
-- weakens the geometric smallness but classifies more interactions as good;
-- decreasing it strengthens HH-good but sends more interactions to HH-bad.
-- Once the physical owner functions are known, the threshold itself should be
-- selected by the reserve problem.
--
-- This module makes that statement exact without inventing functional forms.
-- A `ThresholdTaxProfile` supplies the physically proved HH-good, HH-bad and
-- other-owner taxes as functions of the rational threshold delta.  A certified
-- threshold minimizer is an admissible delta whose total tax is no larger than
-- every other admissible delta.
--
-- If its total is < 1, the optimized decomposition has strict reserve.  If its
-- total is >= 1, *no threshold choice in this physical profile can rescue the
-- architecture*.  Thus threshold optimization becomes a rigorous go/no-go
-- theorem rather than hand tuning.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP

record ThresholdTaxProfile : Set₁ where
  field
    admissibleThreshold : ℚ → Set
    hhGoodEta hhBadEta otherEta : ℚ → ℚ

open ThresholdTaxProfile public

combinedHighHighEta : ThresholdTaxProfile → ℚ → ℚ
combinedHighHighEta profile delta =
  hhGoodEta profile delta + hhBadEta profile delta

totalEtaAt : ThresholdTaxProfile → ℚ → ℚ
totalEtaAt profile delta =
  combinedHighHighEta profile delta + otherEta profile delta

record CertifiedThresholdMinimizer (profile : ThresholdTaxProfile) : Set where
  constructor certified-threshold-minimizer
  field
    selectedThreshold : ℚ
    selectedAdmissible : admissibleThreshold profile selectedThreshold
    globallyMinimalTotal :
      ∀ delta →
      admissibleThreshold profile delta →
      totalEtaAt profile selectedThreshold ≤ totalEtaAt profile delta

open CertifiedThresholdMinimizer public

record StrictOptimizedThresholdReserve
    {profile : ThresholdTaxProfile}
    (certificate : CertifiedThresholdMinimizer profile) : Set where
  field
    optimizedTotalStrict :
      totalEtaAt profile (selectedThreshold certificate) < 1ℚ

open StrictOptimizedThresholdReserve public

NoThresholdCanGiveStrictReserve : ThresholdTaxProfile → Set
NoThresholdCanGiveStrictReserve profile =
  ∀ delta →
  admissibleThreshold profile delta →
  1ℚ ≤ totalEtaAt profile delta

certifiedThresholdAtOrAboveOneIsArchitectureNoGo :
  ∀ {profile} →
  (certificate : CertifiedThresholdMinimizer profile) →
  1ℚ ≤ totalEtaAt profile (selectedThreshold certificate) →
  NoThresholdCanGiveStrictReserve profile
certifiedThresholdAtOrAboveOneIsArchitectureNoGo
    certificate oneBelowMinimum delta admissible =
  ℚP.≤-trans
    oneBelowMinimum
    (globallyMinimalTotal certificate delta admissible)

strictOptimizedThresholdExhibitsStrictAllocation :
  ∀ {profile} {certificate : CertifiedThresholdMinimizer profile} →
  StrictOptimizedThresholdReserve certificate →
  totalEtaAt profile (selectedThreshold certificate) < 1ℚ
strictOptimizedThresholdExhibitsStrictAllocation = optimizedTotalStrict

hhGoodBadThresholdOptimizationTyped : Bool
hhGoodBadThresholdOptimizationTyped = true

physicalThresholdTaxProfileConstructed : Bool
physicalThresholdTaxProfileConstructed = false

physicalCertifiedThresholdMinimizerConstructed : Bool
physicalCertifiedThresholdMinimizerConstructed = false

hhGoodBadThresholdOptimizationTypedIsTrue :
  hhGoodBadThresholdOptimizationTyped ≡ true
hhGoodBadThresholdOptimizationTypedIsTrue = refl
