module DASHI.Physics.Closure.BothwellYe2022ChronometricGeodesyBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_*_; _≤ᵇ_)

import DASHI.Physics.Closure.BothwellYe2022PublishedGradientPayloadExact as Payload
import DASHI.Physics.Closure.BothwellYe2022GeodeticCalibrationExact as Geodetic
import DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge as Redshift
import DASHI.Promotion.SIMetreFromSecondAndCAdapter as Metre

------------------------------------------------------------------------
-- Chronometric-geodesy cross-pollination for the Bothwell/Ye 2022 clock.
--
-- The paper reports a synchronous fractional-frequency uncertainty
--
--   7.6e-21 = 76 * 1e-22.
--
-- The geodetic owner records the NOAA JILA benchmark gravity
--
--   g = 9.796078684 m s^-2
--     = 9796078684 nm s^-2.
--
-- With exact SI c = 299792458 m s^-1 and the weak-field relation
--
--   delta f / f = g h / c^2,
--
-- the height-equivalent scale of that fractional-frequency coordinate is
--
--   h_um = 76 * c^2 / (10^7 * 9796078684)
--        = 6830539358399814064 / 97960786840000000 micrometres
--        ~= 69.7273 micrometres.
--
-- The exact kernel-facing statement below is only the integer bracket
--
--   69 um <= h_equiv <= 70 um.
--
-- This is a conversion of a reported clock uncertainty into a local
-- gravitational height-equivalent coordinate.  It is deliberately NOT an
-- elevation-accuracy claim: survey transfer, geopotential modelling, raw
-- experiment replay, correlations and the full covariance/systematics budget
-- remain separate empirical obligations.
------------------------------------------------------------------------

fractionalFrequencyUncertaintyUnits1eMinus22 : Nat
fractionalFrequencyUncertaintyUnits1eMinus22 = 76

speedOfLightInteger : Nat
speedOfLightInteger = 299792458

sourceGravityNanoMetresPerSecondSquared : Nat
sourceGravityNanoMetresPerSecondSquared = 9796078684

canonicalSourceGravityMatchesGeodeticOwner :
  sourceGravityNanoMetresPerSecondSquared ≡
  Geodetic.sourceGravityNanoMetresPerSecondSquared
canonicalSourceGravityMatchesGeodeticOwner = refl

-- Converting the 1e-22 fractional-frequency unit to micrometres while the
-- gravity carrier is in nm s^-2 leaves the exact scale factor 1 / 10^7.
heightEquivalentMicrometreNumeratorFromInputs : Nat
heightEquivalentMicrometreNumeratorFromInputs =
  fractionalFrequencyUncertaintyUnits1eMinus22 *
  speedOfLightInteger *
  speedOfLightInteger

heightEquivalentMicrometreDenominatorFromInputs : Nat
heightEquivalentMicrometreDenominatorFromInputs =
  10000000 * sourceGravityNanoMetresPerSecondSquared

heightEquivalentMicrometreNumerator : Nat
heightEquivalentMicrometreNumerator = 6830539358399814064

heightEquivalentMicrometreDenominator : Nat
heightEquivalentMicrometreDenominator = 97960786840000000

canonicalHeightEquivalentNumerator :
  heightEquivalentMicrometreNumeratorFromInputs ≡
  heightEquivalentMicrometreNumerator
canonicalHeightEquivalentNumerator = refl

canonicalHeightEquivalentDenominator :
  heightEquivalentMicrometreDenominatorFromInputs ≡
  heightEquivalentMicrometreDenominator
canonicalHeightEquivalentDenominator = refl

heightEquivalentAtLeast69Micrometres : Bool
heightEquivalentAtLeast69Micrometres =
  (69 * heightEquivalentMicrometreDenominator) ≤ᵇ
  heightEquivalentMicrometreNumerator

canonicalHeightEquivalentAtLeast69Micrometres :
  heightEquivalentAtLeast69Micrometres ≡ true
canonicalHeightEquivalentAtLeast69Micrometres = refl

heightEquivalentAtMost70Micrometres : Bool
heightEquivalentAtMost70Micrometres =
  heightEquivalentMicrometreNumerator ≤ᵇ
  (70 * heightEquivalentMicrometreDenominator)

canonicalHeightEquivalentAtMost70Micrometres :
  heightEquivalentAtMost70Micrometres ≡ true
canonicalHeightEquivalentAtMost70Micrometres = refl

record BothwellYe2022ChronometricGeodesyBridge : Set₁ where
  field
    experimentPayload : Payload.PublishedGradientPayload
    experimentPayloadIsCanonical :
      experimentPayload ≡ Payload.canonicalPublishedGradientPayload

    geodeticCalibration : Geodetic.BothwellYe2022GeodeticCalibrationReceipt
    geodeticCalibrationIsCanonical :
      geodeticCalibration ≡ Geodetic.canonicalBothwellYe2022GeodeticCalibrationReceipt

    redshiftLaw : Redshift.QuantumClockProperTimeRedshiftBridge
    redshiftLawIsCanonical :
      redshiftLaw ≡ Redshift.canonicalQuantumClockProperTimeRedshiftBridge

    siMetreAdapter : Metre.SIMetreFromSecondAndCAdapter
    siMetreAdapterIsCanonical :
      siMetreAdapter ≡ Metre.canonicalSIMetreFromSecondAndCAdapter

    reportedClockUncertainty : String
    localGravityCarrier : String
    heightEquivalentCarrier : String
    heightEquivalentBracket : String

    heightEquivalentScaleDerived : Bool
    heightEquivalentScaleDerivedIsTrue :
      heightEquivalentScaleDerived ≡ true

    sameObjectClockGravityMetreWeld : Bool
    sameObjectClockGravityMetreWeldIsTrue :
      sameObjectClockGravityMetreWeld ≡ true

    heightEquivalentClaimedAsElevationAccuracy : Bool
    heightEquivalentClaimedAsElevationAccuracyIsFalse :
      heightEquivalentClaimedAsElevationAccuracy ≡ false

    rawExperimentDataRequiredForAccuracyPromotion : Bool
    rawExperimentDataRequiredForAccuracyPromotionIsTrue :
      rawExperimentDataRequiredForAccuracyPromotion ≡ true

    fullCovarianceRequiredForAccuracyPromotion : Bool
    fullCovarianceRequiredForAccuracyPromotionIsTrue :
      fullCovarianceRequiredForAccuracyPromotion ≡ true

    chronometricGeodesyPromotionAllowed : Bool
    chronometricGeodesyPromotionAllowedIsFalse :
      chronometricGeodesyPromotionAllowed ≡ false

    reading : List String

open BothwellYe2022ChronometricGeodesyBridge public

canonicalBothwellYe2022ChronometricGeodesyBridge :
  BothwellYe2022ChronometricGeodesyBridge
canonicalBothwellYe2022ChronometricGeodesyBridge = record
  { experimentPayload = Payload.canonicalPublishedGradientPayload
  ; experimentPayloadIsCanonical = refl
  ; geodeticCalibration = Geodetic.canonicalBothwellYe2022GeodeticCalibrationReceipt
  ; geodeticCalibrationIsCanonical = refl
  ; redshiftLaw = Redshift.canonicalQuantumClockProperTimeRedshiftBridge
  ; redshiftLawIsCanonical = refl
  ; siMetreAdapter = Metre.canonicalSIMetreFromSecondAndCAdapter
  ; siMetreAdapterIsCanonical = refl
  ; reportedClockUncertainty = "7.6e-21 fractional frequency"
  ; localGravityCarrier = "NOAA JILA S1B60H: 9.796078684 m s^-2"
  ; heightEquivalentCarrier =
      "6830539358399814064 / 97960786840000000 micrometres"
  ; heightEquivalentBracket = "69 micrometres <= h_equiv <= 70 micrometres"
  ; heightEquivalentScaleDerived = true
  ; heightEquivalentScaleDerivedIsTrue = refl
  ; sameObjectClockGravityMetreWeld = true
  ; sameObjectClockGravityMetreWeldIsTrue = refl
  ; heightEquivalentClaimedAsElevationAccuracy = false
  ; heightEquivalentClaimedAsElevationAccuracyIsFalse = refl
  ; rawExperimentDataRequiredForAccuracyPromotion = true
  ; rawExperimentDataRequiredForAccuracyPromotionIsTrue = refl
  ; fullCovarianceRequiredForAccuracyPromotion = true
  ; fullCovarianceRequiredForAccuracyPromotionIsTrue = refl
  ; chronometricGeodesyPromotionAllowed = false
  ; chronometricGeodesyPromotionAllowedIsFalse = refl
  ; reading =
      "The published 7.6e-21 clock coordinate, NOAA local gravity and the exact SI metre/c carrier now inhabit one explicit conversion surface."
      ∷ "Exact integer cross-products place its local height-equivalent scale between 69 and 70 micrometres."
      ∷ "This expresses clock sensitivity in a spatial unit; it does not establish 70-micrometre elevation accuracy, geopotential-model accuracy, or a completed geodetic survey."
      ∷ "Chronometric-geodesy promotion remains fail-closed until experiment replay, covariance/systematics and survey-transfer obligations are paid."
      ∷ []
  }

canonicalHeightEquivalentIsNotElevationAccuracy :
  heightEquivalentClaimedAsElevationAccuracy
    canonicalBothwellYe2022ChronometricGeodesyBridge
  ≡ false
canonicalHeightEquivalentIsNotElevationAccuracy = refl

canonicalChronometricGeodesyPromotionStillClosed :
  chronometricGeodesyPromotionAllowed
    canonicalBothwellYe2022ChronometricGeodesyBridge
  ≡ false
canonicalChronometricGeodesyPromotionStillClosed = refl
