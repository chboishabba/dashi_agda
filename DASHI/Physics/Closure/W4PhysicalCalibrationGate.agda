module DASHI.Physics.Closure.W4PhysicalCalibrationGate where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.ChemistryStrictPhysicalSemanticsBlocker as Blocker
import DASHI.Physics.Closure.W4StrictPhysicalScaleSettingLaneObligation as Obligation
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Boundary
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next

------------------------------------------------------------------------
-- W4 physical calibration gate.
--
-- The current W4 surrogate gives a Nat-valued, dimensionless scale-like
-- observable.  This module records the extra typed surface needed before
-- that surrogate can be promoted into strict physical scale-setting:
-- a physical calibration authority token, a physical unit carrier, a
-- calibration map from Nat into those units, a dimensional-preservation law,
-- and an explicit boundary that spectra, bonding, and empirical validation
-- remain downstream obligations.  The authority token deliberately has no
-- constructor here, so the surrogate cannot be promoted by choosing `Nat` as
-- its own unit system.

data Candidate256PhysicalCalibrationAuthorityToken : Set where

record Candidate256PhysicalUnitCalibration : Setω where
  field
    calibrationAuthority :
      Candidate256PhysicalCalibrationAuthorityToken

    physicalUnitCarrier : Set

    calibrationMap :
      Boundary.SurrogateScaleCarrier →
      physicalUnitCarrier

    calibratedQuotientScaleMap :
      Boundary.Candidate256QuotientClass →
      physicalUnitCarrier

    calibratedScaleMapFactorsThroughSurrogate :
      (q : Boundary.Candidate256QuotientClass) →
      calibratedQuotientScaleMap q
      ≡
      calibrationMap (Boundary.candidate256SurrogateScale q)

    dimensionalPreservationLaw :
      Handoff.QuotientLawAtWitness
        Next.canonicalCandidate256QuotientLaw →
      Set

    dimensionalPreservationAtWitness :
      (law :
        Handoff.QuotientLawAtWitness
          Next.canonicalCandidate256QuotientLaw) →
      dimensionalPreservationLaw law

    physicalUnitCarrierLabel : String
    calibrationMapLabel : String
    dimensionalPreservationLabel : String

candidate256PhysicalCalibrationLaneFields :
  Candidate256PhysicalUnitCalibration →
  Obligation.Candidate256ScaleSettingLaneFields
candidate256PhysicalCalibrationLaneFields calibration =
  record
    { physicalScaleCarrier =
        Candidate256PhysicalUnitCalibration.physicalUnitCarrier calibration
    ; quotientClassScaleMap =
        Candidate256PhysicalUnitCalibration.calibratedQuotientScaleMap
          calibration
    ; LchemScalePreservationLaw =
        Candidate256PhysicalUnitCalibration.dimensionalPreservationLaw
          calibration
    }

candidate256PhysicalCalibrationDischargesScaleSetting :
  (calibration : Candidate256PhysicalUnitCalibration) →
  Obligation.candidate256ScaleSettingFieldsNeeded
    (candidate256PhysicalCalibrationLaneFields calibration)
candidate256PhysicalCalibrationDischargesScaleSetting calibration =
  Candidate256PhysicalUnitCalibration.dimensionalPreservationAtWitness
    calibration

record Candidate256PhysicalCalibrationGate : Setω where
  field
    surrogateBoundary :
      Boundary.Candidate256SurrogateScaleSettingBoundaryReceipt

    calibration :
      Candidate256PhysicalUnitCalibration

    strictScaleSettingLaw :
      Obligation.candidate256ScaleSettingFieldsNeeded
        (candidate256PhysicalCalibrationLaneFields calibration)

    downstreamStillMissing :
      List Blocker.StrictPhysicalMissingIngredient

    downstreamBoundary :
      List String

    noSpectraBondingEmpiricalPromotionHere :
      List String

data Candidate256PhysicalCalibrationBlockedIngredient : Set where
  surrogateNatScaleAvailable :
    Candidate256PhysicalCalibrationBlockedIngredient
  missingPhysicalUnitCarrier :
    Candidate256PhysicalCalibrationBlockedIngredient
  missingNatToPhysicalUnitCalibrationMap :
    Candidate256PhysicalCalibrationBlockedIngredient
  missingDimensionalPreservationLaw :
    Candidate256PhysicalCalibrationBlockedIngredient
  spectraBondingEmpiricalRemainDownstream :
    Candidate256PhysicalCalibrationBlockedIngredient

record Candidate256PhysicalCalibrationCurrentStatus : Setω where
  field
    surrogateBoundary :
      Boundary.Candidate256SurrogateScaleSettingBoundaryReceipt

    surrogateCarrier :
      Set

    surrogateCarrierIsNat :
      surrogateCarrier ≡ Nat

    currentSurrogateLaneFields :
      Obligation.Candidate256ScaleSettingLaneFields

    currentSurrogateLaw :
      Obligation.candidate256ScaleSettingFieldsNeeded
        currentSurrogateLaneFields

    blockedIngredients :
      List Candidate256PhysicalCalibrationBlockedIngredient

    strictPhysicalMissingIngredients :
      List Blocker.StrictPhysicalMissingIngredient

    requiredPhysicalUnitCarrier : String
    requiredCalibrationMap : String
    requiredDimensionalPreservationLaw : String

    currentBoundary :
      List String

    noPhysicalCalibrationGateInhabited :
      List String

canonicalCandidate256PhysicalCalibrationCurrentStatus :
  Candidate256PhysicalCalibrationCurrentStatus
canonicalCandidate256PhysicalCalibrationCurrentStatus =
  record
    { surrogateBoundary =
        Boundary.canonicalCandidate256SurrogateScaleSettingBoundaryReceipt
    ; surrogateCarrier =
        Boundary.SurrogateScaleCarrier
    ; surrogateCarrierIsNat =
        refl
    ; currentSurrogateLaneFields =
        Boundary.candidate256SurrogateScaleSettingLaneFields
    ; currentSurrogateLaw =
        Boundary.candidate256SurrogateScaleSettingFieldsNeeded
    ; blockedIngredients =
        surrogateNatScaleAvailable
        ∷ missingPhysicalUnitCarrier
        ∷ missingNatToPhysicalUnitCalibrationMap
        ∷ missingDimensionalPreservationLaw
        ∷ spectraBondingEmpiricalRemainDownstream
        ∷ []
    ; strictPhysicalMissingIngredients =
        Blocker.missingScaleSettingLaw
        ∷ Blocker.missingSpectralObservableMap
        ∷ Blocker.missingBondingInterpretation
        ∷ Blocker.missingEmpiricalPhysicalValidation
        ∷ []
    ; requiredPhysicalUnitCarrier =
        "provide a physical unit carrier distinct from the dimensionless Nat surrogate"
    ; requiredCalibrationMap =
        "provide a calibration map from surrogate Nat scale values into physical units"
    ; requiredDimensionalPreservationLaw =
        "prove the calibrated scale map preserves the Candidate256 L_chem witness dimensionally"
    ; currentBoundary =
        "Candidate256 currently has a Nat-valued dimensionless surrogate scale"
        ∷ "No physical unit carrier is supplied for the Nat surrogate"
        ∷ "No Nat-to-unit calibration map is supplied"
        ∷ "No dimensional-preservation law is supplied"
        ∷ "Spectral observable mapping, bonding interpretation, and empirical physical validation remain downstream"
        ∷ []
    ; noPhysicalCalibrationGateInhabited =
        "The current status does not inhabit Candidate256PhysicalCalibrationGate"
        ∷ "The surrogate scale-setting fields are recorded only as dimensionless current inputs"
        ∷ "Strict physical scale-setting remains blocked until units, calibration, and dimensional preservation are supplied"
        ∷ "No spectra, bonding, empirical validation, or physical closure promotion is made here"
        ∷ []
    }

candidate256PhysicalCalibrationDownstreamBoundary :
  List Blocker.StrictPhysicalMissingIngredient
candidate256PhysicalCalibrationDownstreamBoundary =
  Blocker.missingSpectralObservableMap
  ∷ Blocker.missingBondingInterpretation
  ∷ Blocker.missingEmpiricalPhysicalValidation
  ∷ []
