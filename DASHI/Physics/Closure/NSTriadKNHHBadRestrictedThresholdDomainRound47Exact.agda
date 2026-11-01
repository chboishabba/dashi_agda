module DASHI.Physics.Closure.NSTriadKNHHBadRestrictedThresholdDomainRound47Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- A downstream argument may need uniformity only on a threshold interval
-- [delta_0,delta_1] with delta_0>0.  This module makes that weaker obligation
-- explicit instead of silently demanding uniformity as delta -> 0.
--
-- A restricted common ceiling is enough to define one threshold-independent
-- HH-bad eta for every physical threshold actually used inside the interval.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Scale
import DASHI.Physics.Closure.NSTriadKNHHBadThresholdUniformityRound46Exact as Uniform

record PositiveThresholdInterval : Set where
  field
    lower upper : ℚ
    lowerPositive : 0ℚ < lower
    lowerBelowUpper : lower ≤ upper

open PositiveThresholdInterval public

InThresholdInterval :
  PositiveThresholdInterval → Threshold.PositiveThreshold → Set
InThresholdInterval interval parameter =
  (lower interval ≤ Threshold.threshold parameter)
  × (Threshold.threshold parameter ≤ upper interval)

record RestrictedThresholdUniformProfile
    (indexed : Uniform.ThresholdIndexedHHBadProfiles)
    (interval : PositiveThresholdInterval) : Set where
  field
    restrictedCeiling : ℚ
    restrictedCeilingNonnegative : 0ℚ ≤ restrictedCeiling
    restrictedBound : ∀ parameter shell →
      InThresholdInterval interval parameter →
      Uniform.normalizedCoefficient indexed parameter shell
      ≤ restrictedCeiling

open RestrictedThresholdUniformProfile public

restrictedCanonicalEta :
  ∀ {indexed interval} →
  RestrictedThresholdUniformProfile indexed interval → ℚ
restrictedCanonicalEta restricted =
  Sharp.two * restrictedCeiling restricted

restrictedCanonicalEtaNonnegative :
  ∀ {indexed interval}
    (restricted : RestrictedThresholdUniformProfile indexed interval) →
  0ℚ ≤ restrictedCanonicalEta restricted
restrictedCanonicalEtaNonnegative restricted =
  let instance
    twoNNI = nonNegative Scale.twoNonnegative
    ceilingNNI = nonNegative (restrictedCeilingNonnegative restricted)
    productNNI =
      ℚP.nonNeg*nonNeg⇒nonNeg Sharp.two (restrictedCeiling restricted)
  in
  ℚP.nonNegative⁻¹ (restrictedCanonicalEta restricted)

restrictedProfileGivesThresholdIndependentEtaInsideDomain :
  ∀ {indexed interval}
    (restricted : RestrictedThresholdUniformProfile indexed interval)
    parameter shell →
  InThresholdInterval interval parameter →
  Uniform.normalizedCoefficient indexed parameter shell
  ≤ restrictedCeiling restricted
restrictedProfileGivesThresholdIndependentEtaInsideDomain = restrictedBound

restrictedThresholdUniformityIsSufficientLanguage : Bool
restrictedThresholdUniformityIsSufficientLanguage = true

globalThresholdUniformityNotAssumed : Bool
globalThresholdUniformityNotAssumed = true

restrictedThresholdUniformityIsSufficientLanguageIsTrue :
  restrictedThresholdUniformityIsSufficientLanguage ≡ true
restrictedThresholdUniformityIsSufficientLanguageIsTrue = refl
