module DASHI.Physics.Closure.EmpiricalCalibrationBridgeUnits where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Option B empirical calibration bridge with explicit units.
--
-- This module is only a typed surface.  It does not choose SI units, numeric
-- constants, or empirical calibration data.  Numeric claims require the
-- constructorless authority token below, so internal dimensionless energy
-- cannot be silently promoted into measured quantities.

data ExternalCalibrationAuthorityToken : Set where

record DimensionedUnitSurface : Setω where
  field
    UnitCarrier : Set
    DimensionCarrier : Set

    dimensionOfUnit :
      UnitCarrier →
      DimensionCarrier

    unitCarrierLabel : String
    dimensionCarrierLabel : String

record EmpiricalCalibrationScaleEvidence
  (ScaleCarrier : Set)
  (CalibrationToken : Set)
  : Set where
  field
    scaleEvidence :
      ScaleCarrier ⊎ CalibrationToken

record NumericCalibrationClaim : Setω where
  field
    externalAuthority :
      ExternalCalibrationAuthorityToken

    numericCarrier : Set
    numericValueLabel : String
    authorityLabel : String

record UnitPreservingEmpiricalCalibrationBridge : Setω where
  field
    internalEnergyCarrier : Set
    measuredQuantityCarrier : Set

    unitSurface :
      DimensionedUnitSurface

    internalEnergyUnit :
      internalEnergyCarrier →
      DimensionedUnitSurface.UnitCarrier unitSurface

    measuredQuantityUnit :
      measuredQuantityCarrier →
      DimensionedUnitSurface.UnitCarrier unitSurface

    calibrationMap :
      internalEnergyCarrier →
      measuredQuantityCarrier

    dimensionPreservation :
      (e : internalEnergyCarrier) →
      DimensionedUnitSurface.dimensionOfUnit unitSurface
        (measuredQuantityUnit (calibrationMap e))
      ≡
      DimensionedUnitSurface.dimensionOfUnit unitSurface
        (internalEnergyUnit e)

    internalOrder :
      internalEnergyCarrier →
      internalEnergyCarrier →
      Set

    measuredOrder :
      measuredQuantityCarrier →
      measuredQuantityCarrier →
      Set

    monotonicity :
      (e₁ e₂ : internalEnergyCarrier) →
      internalOrder e₁ e₂ →
      measuredOrder (calibrationMap e₁) (calibrationMap e₂)

    scaleCarrier : Set
    calibrationTokenCarrier : Set

    scaleOrCalibrationToken :
      EmpiricalCalibrationScaleEvidence
        scaleCarrier
        calibrationTokenCarrier

    numericClaim :
      NumericCalibrationClaim →
      Set

    bridgeLabel : String
    unitPreservationLabel : String
    monotonicityLabel : String
    authorityBoundaryLabel : String

externalCalibrationAuthorityImpossibleHere :
  ExternalCalibrationAuthorityToken →
  ⊥
externalCalibrationAuthorityImpossibleHere ()

numericCalibrationClaimImpossibleHere :
  NumericCalibrationClaim →
  ⊥
numericCalibrationClaimImpossibleHere claim =
  externalCalibrationAuthorityImpossibleHere
    (NumericCalibrationClaim.externalAuthority claim)

data EmpiricalCalibrationBridgeUnitsMissingIngredient : Set where
  missingPhysicalUnitCarrier :
    EmpiricalCalibrationBridgeUnitsMissingIngredient
  missingDimensionCarrier :
    EmpiricalCalibrationBridgeUnitsMissingIngredient
  missingInternalEnergyUnitAssignment :
    EmpiricalCalibrationBridgeUnitsMissingIngredient
  missingMeasuredQuantityUnitAssignment :
    EmpiricalCalibrationBridgeUnitsMissingIngredient
  missingDimensionPreservationLaw :
    EmpiricalCalibrationBridgeUnitsMissingIngredient
  missingScaleFactorOrCalibrationToken :
    EmpiricalCalibrationBridgeUnitsMissingIngredient
  missingMonotonicityLaw :
    EmpiricalCalibrationBridgeUnitsMissingIngredient
  missingExternalAuthorityForNumericClaims :
    EmpiricalCalibrationBridgeUnitsMissingIngredient

data EmpiricalCalibrationBridgeUnitsStatus : Set where
  blockedAwaitingExternalUnitCalibration :
    EmpiricalCalibrationBridgeUnitsStatus

record EmpiricalCalibrationBridgeUnitsCurrentStatus : Setω where
  field
    currentStatus :
      EmpiricalCalibrationBridgeUnitsStatus

    missingIngredients :
      List EmpiricalCalibrationBridgeUnitsMissingIngredient

    requiredUnitSurface : String
    requiredDimensionPreservation : String
    requiredScaleEvidence : String
    requiredMonotonicity : String
    requiredExternalAuthority : String

    noPromotionBoundary :
      List String

    impossibleAuthorityHere :
      ExternalCalibrationAuthorityToken →
      ⊥

    impossibleNumericClaimHere :
      NumericCalibrationClaim →
      ⊥

canonicalEmpiricalCalibrationBridgeUnitsCurrentStatus :
  EmpiricalCalibrationBridgeUnitsCurrentStatus
canonicalEmpiricalCalibrationBridgeUnitsCurrentStatus =
  record
    { currentStatus =
        blockedAwaitingExternalUnitCalibration
    ; missingIngredients =
        missingPhysicalUnitCarrier
        ∷ missingDimensionCarrier
        ∷ missingInternalEnergyUnitAssignment
        ∷ missingMeasuredQuantityUnitAssignment
        ∷ missingDimensionPreservationLaw
        ∷ missingScaleFactorOrCalibrationToken
        ∷ missingMonotonicityLaw
        ∷ missingExternalAuthorityForNumericClaims
        ∷ []
    ; requiredUnitSurface =
        "supply a unit carrier and dimension carrier for the measured quantity surface"
    ; requiredDimensionPreservation =
        "prove that calibration preserves the dimension of every internal energy input"
    ; requiredScaleEvidence =
        "supply either a scale factor carrier value or a calibration token carrier value"
    ; requiredMonotonicity =
        "prove calibration is monotone from the internal energy order to the measured order"
    ; requiredExternalAuthority =
        "supply ExternalCalibrationAuthorityToken before any numeric calibration value is claimed"
    ; noPromotionBoundary =
        "This module does not choose units, dimensions, numeric constants, or datasets"
        ∷ "ExternalCalibrationAuthorityToken has no constructor in this module"
        ∷ "NumericCalibrationClaim is impossible here without external authority"
        ∷ "Internal energy is not promoted to a measured physical quantity without unit and dimension preservation"
        ∷ "W4 chemistry and W5 physics remain blocked on external unit calibration and validation"
        ∷ []
    ; impossibleAuthorityHere =
        externalCalibrationAuthorityImpossibleHere
    ; impossibleNumericClaimHere =
        numericCalibrationClaimImpossibleHere
    }
