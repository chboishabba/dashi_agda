module DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.W4PhysicalCalibrationGate as Gate
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next
import DASHI.Physics.Closure.W4StrictPhysicalScaleSettingLaneObligation as Scale
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Surrogate

------------------------------------------------------------------------
-- W4m external receipt obligation.
--
-- W4PhysicalCalibrationGate keeps the physical calibration authority token
-- constructorless in-repo.  This module therefore records the narrow shape
-- of the external receipt that would be needed later, without constructing
-- that token and without promoting the current Nat surrogate.

record Candidate256PhysicalCalibrationExternalReceipt : Setω where
  field
    calibrationAuthority :
      Gate.Candidate256PhysicalCalibrationAuthorityToken

    physicalUnitCarrier : Set

    natToUnitCalibrationMap :
      Nat →
      physicalUnitCarrier

    calibratedQuotientScaleMap :
      Surrogate.Candidate256QuotientClass →
      physicalUnitCarrier

    calibratedScaleMapFactorsThroughNat :
      (q : Surrogate.Candidate256QuotientClass) →
      calibratedQuotientScaleMap q
      ≡
      natToUnitCalibrationMap (Surrogate.candidate256SurrogateScale q)

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
    natToUnitCalibrationMapLabel : String
    calibratedQuotientScaleMapLabel : String
    factorizationLabel : String
    dimensionalPreservationLabel : String

externalReceiptToPhysicalUnitCalibration :
  Candidate256PhysicalCalibrationExternalReceipt →
  Gate.Candidate256PhysicalUnitCalibration
externalReceiptToPhysicalUnitCalibration receipt =
  record
    { calibrationAuthority =
        Candidate256PhysicalCalibrationExternalReceipt.calibrationAuthority
          receipt
    ; physicalUnitCarrier =
        Candidate256PhysicalCalibrationExternalReceipt.physicalUnitCarrier
          receipt
    ; calibrationMap =
        Candidate256PhysicalCalibrationExternalReceipt.natToUnitCalibrationMap
          receipt
    ; calibratedQuotientScaleMap =
        Candidate256PhysicalCalibrationExternalReceipt.calibratedQuotientScaleMap
          receipt
    ; calibratedScaleMapFactorsThroughSurrogate =
        Candidate256PhysicalCalibrationExternalReceipt.calibratedScaleMapFactorsThroughNat
          receipt
    ; dimensionalPreservationLaw =
        Candidate256PhysicalCalibrationExternalReceipt.dimensionalPreservationLaw
          receipt
    ; dimensionalPreservationAtWitness =
        Candidate256PhysicalCalibrationExternalReceipt.dimensionalPreservationAtWitness
          receipt
    ; physicalUnitCarrierLabel =
        Candidate256PhysicalCalibrationExternalReceipt.physicalUnitCarrierLabel
          receipt
    ; calibrationMapLabel =
        Candidate256PhysicalCalibrationExternalReceipt.natToUnitCalibrationMapLabel
          receipt
    ; dimensionalPreservationLabel =
        Candidate256PhysicalCalibrationExternalReceipt.dimensionalPreservationLabel
          receipt
    }

externalReceiptToScaleSettingLaneFields :
  Candidate256PhysicalCalibrationExternalReceipt →
  Scale.Candidate256ScaleSettingLaneFields
externalReceiptToScaleSettingLaneFields receipt =
  Gate.candidate256PhysicalCalibrationLaneFields
    (externalReceiptToPhysicalUnitCalibration receipt)

externalReceiptDischargesScaleSetting :
  (receipt : Candidate256PhysicalCalibrationExternalReceipt) →
  Scale.candidate256ScaleSettingFieldsNeeded
    (externalReceiptToScaleSettingLaneFields receipt)
externalReceiptDischargesScaleSetting receipt =
  Gate.candidate256PhysicalCalibrationDischargesScaleSetting
    (externalReceiptToPhysicalUnitCalibration receipt)

data Candidate256PhysicalCalibrationExternalBlockedField : Set where
  missingExternalCalibrationAuthorityToken :
    Candidate256PhysicalCalibrationExternalBlockedField
  missingExternalPhysicalUnitCarrier :
    Candidate256PhysicalCalibrationExternalBlockedField
  missingExternalNatToUnitCalibrationMap :
    Candidate256PhysicalCalibrationExternalBlockedField
  missingExternalCalibratedQuotientScaleMap :
    Candidate256PhysicalCalibrationExternalBlockedField
  missingExternalFactorizationLaw :
    Candidate256PhysicalCalibrationExternalBlockedField
  missingExternalDimensionalPreservationLaw :
    Candidate256PhysicalCalibrationExternalBlockedField
  missingExternalDimensionalPreservationAtWitness :
    Candidate256PhysicalCalibrationExternalBlockedField

candidate256PhysicalCalibrationAuthorityTokenImpossibleHere :
  Gate.Candidate256PhysicalCalibrationAuthorityToken →
  ⊥
candidate256PhysicalCalibrationAuthorityTokenImpossibleHere ()

candidate256PhysicalCalibrationExternalReceiptImpossibleHere :
  Candidate256PhysicalCalibrationExternalReceipt →
  ⊥
candidate256PhysicalCalibrationExternalReceiptImpossibleHere receipt =
  candidate256PhysicalCalibrationAuthorityTokenImpossibleHere
    (Candidate256PhysicalCalibrationExternalReceipt.calibrationAuthority
      receipt)

canonicalCandidate256PhysicalCalibrationExternalBlockedFields :
  List Candidate256PhysicalCalibrationExternalBlockedField
canonicalCandidate256PhysicalCalibrationExternalBlockedFields =
  missingExternalCalibrationAuthorityToken
  ∷ missingExternalPhysicalUnitCarrier
  ∷ missingExternalNatToUnitCalibrationMap
  ∷ missingExternalCalibratedQuotientScaleMap
  ∷ missingExternalFactorizationLaw
  ∷ missingExternalDimensionalPreservationLaw
  ∷ missingExternalDimensionalPreservationAtWitness
  ∷ []

record Candidate256PhysicalCalibrationExternalReceiptCurrentStatus : Setω where
  field
    gateStatus :
      Gate.Candidate256PhysicalCalibrationCurrentStatus

    scaleSettingObligation :
      Scale.Candidate256ScaleSettingLaneObligationReceipt

    scaleSettingStatus :
      Scale.Candidate256ScaleSettingLaneStatus

    blockedExternalFields :
      List Candidate256PhysicalCalibrationExternalBlockedField

    gateBlockedIngredients :
      List Gate.Candidate256PhysicalCalibrationBlockedIngredient

    requiredExternalReceipt : String
    authorityBoundary : String
    calibrationBoundary : String
    factorizationBoundary : String
    dimensionalBoundary : String
    downstreamPhysicalBoundary : String

    noAuthorityConstructedHere :
      List String

    noPromotionBoundary :
      List String

    impossibleWithoutExternalAuthority :
      Gate.Candidate256PhysicalCalibrationAuthorityToken →
      ⊥

    impossibleReceiptWithoutExternalAuthority :
      Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus :
  Candidate256PhysicalCalibrationExternalReceiptCurrentStatus
canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus =
  record
    { gateStatus =
        Gate.canonicalCandidate256PhysicalCalibrationCurrentStatus
    ; scaleSettingObligation =
        Scale.canonicalCandidate256ScaleSettingLaneObligationReceipt
    ; scaleSettingStatus =
        Scale.candidate256ScaleSettingObligationStatus
    ; blockedExternalFields =
        canonicalCandidate256PhysicalCalibrationExternalBlockedFields
    ; gateBlockedIngredients =
        Gate.Candidate256PhysicalCalibrationCurrentStatus.blockedIngredients
          Gate.canonicalCandidate256PhysicalCalibrationCurrentStatus
    ; requiredExternalReceipt =
        "provide an upstream external receipt carrying authority, units, calibration, factorization, and dimensional preservation"
    ; authorityBoundary =
        "Candidate256PhysicalCalibrationAuthorityToken has no constructor in the current repo"
    ; calibrationBoundary =
        "physical unit carrier, Nat-to-unit calibration map, and calibrated quotient scale map remain external obligations"
    ; factorizationBoundary =
        "the calibrated quotient scale map must factor through candidate256SurrogateScale before it can feed the physical scale-setting lane"
    ; dimensionalBoundary =
        "dimensional preservation requires both the law family and its inhabitant at every Candidate256 quotient-law witness"
    ; downstreamPhysicalBoundary =
        "spectral observable mapping, bonding interpretation, and empirical physical validation remain later strict-physical lanes after calibration"
    ; noAuthorityConstructedHere =
        "This module does not construct Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "This module does not inhabit Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "Any total receipt construction is impossible here until an external authority token is supplied outside this constructorless boundary"
        ∷ []
    ; noPromotionBoundary =
        "The current status is obligations-needed only"
        ∷ "The Nat surrogate is not promoted to a physical unit system"
        ∷ "No Candidate256PhysicalCalibrationGate value is constructed here"
        ∷ "No spectra, bonding, empirical validation, or physical closure claim is made here"
        ∷ []
    ; impossibleWithoutExternalAuthority =
        candidate256PhysicalCalibrationAuthorityTokenImpossibleHere
    ; impossibleReceiptWithoutExternalAuthority =
        candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    }
