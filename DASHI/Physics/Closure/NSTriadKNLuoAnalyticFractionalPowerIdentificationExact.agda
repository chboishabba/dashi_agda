module DASHI.Physics.Closure.NSTriadKNLuoAnalyticFractionalPowerIdentificationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Reduce the final alpha=3/2 fractional-power identification to three exact
-- and independently auditable equalities: the dyadic shift law, specialization
-- of 1-alpha to -1/2, and evaluation of the four-shell factor as 1/4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geometric
import DASHI.Physics.Closure.NSTriadKNLuoFourAlignedAlphaThreeHalvesSummabilityExact as Summability

record AnalyticFractionalPowerPrimitiveInputs : Set₁ where
  field
    analyticFourShellRatio : ℚ
    dyadicShiftRatio : ℚ
    alphaThreeHalvesSpecializedRatio : ℚ

    analyticRatioFromDyadicShiftLaw :
      analyticFourShellRatio ≡ dyadicShiftRatio

    dyadicShiftRatioFromAlphaSpecialization :
      dyadicShiftRatio ≡ alphaThreeHalvesSpecializedRatio

    alphaThreeHalvesFourShiftFactorIsQuarter :
      alphaThreeHalvesSpecializedRatio ≡ Geometric.quarter

    DyadicScaleDefinition : Set
    dyadicScaleDefinition : DyadicScaleDefinition

    DyadicShiftLaw : Set
    dyadicShiftLaw : DyadicShiftLaw

    RealPowerIntegerExponentAgreement : Set
    realPowerIntegerExponentAgreement :
      RealPowerIntegerExponentAgreement

    RealPowerRationalExponentAgreement : Set
    realPowerRationalExponentAgreement :
      RealPowerRationalExponentAgreement

    AlphaThreeHalvesExponentMeaning : Set
    alphaThreeHalvesExponentMeaning :
      AlphaThreeHalvesExponentMeaning

    FractionalPowerTermsNonnegative : Set
    fractionalPowerTermsNonnegative :
      FractionalPowerTermsNonnegative

open AnalyticFractionalPowerPrimitiveInputs public

analyticFourShellRatioIsQuarter :
  (inputs : AnalyticFractionalPowerPrimitiveInputs) →
  analyticFourShellRatio inputs ≡ Geometric.quarter
analyticFourShellRatioIsQuarter inputs =
  trans
    (analyticRatioFromDyadicShiftLaw inputs)
    (trans
      (dyadicShiftRatioFromAlphaSpecialization inputs)
      (alphaThreeHalvesFourShiftFactorIsQuarter inputs))

analyticFourShellRatioIdentification :
  AnalyticFractionalPowerPrimitiveInputs →
  Summability.AnalyticFourShellRatioIdentification
analyticFourShellRatioIdentification inputs = record
  { analyticFourShellRatio = analyticFourShellRatio inputs
  ; analyticFourShellRatioMeaning = analyticFourShellRatioIsQuarter inputs
  ; AnalyticFractionalPowerMeaning =
      AlphaThreeHalvesExponentMeaning inputs
  ; analyticFractionalPowerMeaning =
      alphaThreeHalvesExponentMeaning inputs
  }

analyticFractionalPowerReductionConstructed : Bool
analyticFractionalPowerReductionConstructed = true

threePrimitiveEqualitiesSufficeForQuarterRatio : Bool
threePrimitiveEqualitiesSufficeForQuarterRatio = true

analyticFractionalPowerReductionConstructedIsTrue :
  analyticFractionalPowerReductionConstructed ≡ true
analyticFractionalPowerReductionConstructedIsTrue = refl

threePrimitiveEqualitiesSufficeForQuarterRatioIsTrue :
  threePrimitiveEqualitiesSufficeForQuarterRatio ≡ true
threePrimitiveEqualitiesSufficeForQuarterRatioIsTrue = refl
