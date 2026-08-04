module DASHI.Physics.Closure.NSTriadKNLuoFourAlignedAlphaThreeHalvesSummabilityExact where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- PURPOSE
-- Close the rational geometric summability algebra for alpha=3/2 on
-- four-aligned shell blocks. The remaining bridge is the explicit
-- identification of the analytic fractional-power coefficient with 1/4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geometric
import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesConstantsExact as Alpha

fourAlignedAlphaThreeHalvesRatio : ℚ
fourAlignedAlphaThreeHalvesRatio = Geometric.quarter

fourAlignedAlphaThreeHalvesPrefix : Nat → ℚ
fourAlignedAlphaThreeHalvesPrefix cutoff =
  Geometric.partialSum fourAlignedAlphaThreeHalvesRatio cutoff

fourAlignedAlphaThreeHalvesPrefixBound :
  ∀ cutoff →
  fourAlignedAlphaThreeHalvesPrefix cutoff
  ≤ Geometric.fourThirds
fourAlignedAlphaThreeHalvesPrefixBound =
  Geometric.quarterPartialSumBound

record AnalyticFourShellRatioIdentification : Set₁ where
  field
    analyticFourShellRatio : ℚ
    analyticFourShellRatioMeaning :
      analyticFourShellRatio ≡ fourAlignedAlphaThreeHalvesRatio
    AnalyticFractionalPowerMeaning : Set
    analyticFractionalPowerMeaning : AnalyticFractionalPowerMeaning

open AnalyticFourShellRatioIdentification public

identifiedFourShellPrefixBound :
  (identification : AnalyticFourShellRatioIdentification) →
  (cutoff : Nat) →
  Geometric.partialSum (analyticFourShellRatio identification) cutoff
  ≤ Geometric.fourThirds
identifiedFourShellPrefixBound identification cutoff
  rewrite analyticFourShellRatioMeaning identification =
  fourAlignedAlphaThreeHalvesPrefixBound cutoff

record FourAlignedAlphaThreeHalvesSummability
    (shift : Alpha.FourAlignedLuoShift) : Set₁ where
  field
    ratioIdentification : AnalyticFourShellRatioIdentification
    everyFiniteBlockPrefixBound :
      (cutoff : Nat) →
      Geometric.partialSum
        (analyticFourShellRatio ratioIdentification) cutoff
      ≤ Geometric.fourThirds

open FourAlignedAlphaThreeHalvesSummability public

fourAlignedSummability :
  (shift : Alpha.FourAlignedLuoShift) →
  (identification : AnalyticFourShellRatioIdentification) →
  FourAlignedAlphaThreeHalvesSummability shift
fourAlignedSummability shift identification = record
  { ratioIdentification = identification
  ; everyFiniteBlockPrefixBound = identifiedFourShellPrefixBound identification
  }

alphaThreeHalvesFourAlignedGeometricSummabilityClosed : Bool
alphaThreeHalvesFourAlignedGeometricSummabilityClosed = true

onlyFractionalPowerIdentificationRemains : Bool
onlyFractionalPowerIdentificationRemains = true

alphaThreeHalvesFourAlignedGeometricSummabilityClosedIsTrue :
  alphaThreeHalvesFourAlignedGeometricSummabilityClosed ≡ true
alphaThreeHalvesFourAlignedGeometricSummabilityClosedIsTrue = refl

onlyFractionalPowerIdentificationRemainsIsTrue :
  onlyFractionalPowerIdentificationRemains ≡ true
onlyFractionalPowerIdentificationRemainsIsTrue = refl
