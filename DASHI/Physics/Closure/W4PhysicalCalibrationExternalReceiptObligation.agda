module DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
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

record Candidate256PhysicalCalibrationDimensionVector : Set where
  field
    lengthPositiveExponent : Nat
    lengthNegativeExponent : Nat
    massPositiveExponent : Nat
    massNegativeExponent : Nat
    timePositiveExponent : Nat
    timeNegativeExponent : Nat
    electricCurrentPositiveExponent : Nat
    electricCurrentNegativeExponent : Nat
    thermodynamicTemperaturePositiveExponent : Nat
    thermodynamicTemperatureNegativeExponent : Nat
    amountOfSubstancePositiveExponent : Nat
    amountOfSubstanceNegativeExponent : Nat
    luminousIntensityPositiveExponent : Nat
    luminousIntensityNegativeExponent : Nat

open Candidate256PhysicalCalibrationDimensionVector public

candidate256UnloadedDimensionVector :
  Candidate256PhysicalCalibrationDimensionVector
candidate256UnloadedDimensionVector = record
  { lengthPositiveExponent = zero
  ; lengthNegativeExponent = zero
  ; massPositiveExponent = zero
  ; massNegativeExponent = zero
  ; timePositiveExponent = zero
  ; timeNegativeExponent = zero
  ; electricCurrentPositiveExponent = zero
  ; electricCurrentNegativeExponent = zero
  ; thermodynamicTemperaturePositiveExponent = zero
  ; thermodynamicTemperatureNegativeExponent = zero
  ; amountOfSubstancePositiveExponent = zero
  ; amountOfSubstanceNegativeExponent = zero
  ; luminousIntensityPositiveExponent = zero
  ; luminousIntensityNegativeExponent = zero
  }

record Candidate256PhysicalCalibrationFactorizationChecker
  (physicalUnitCarrier : Set) : Set where
  field
    natToUnitCandidate :
      Nat →
      physicalUnitCarrier

    quotientScaleCandidate :
      Surrogate.Candidate256QuotientClass →
      physicalUnitCarrier

    factorsThroughCandidate256Surrogate :
      (q : Surrogate.Candidate256QuotientClass) →
      quotientScaleCandidate q
      ≡
      natToUnitCandidate (Surrogate.candidate256SurrogateScale q)

    factorizationCheckerLabel : String

open Candidate256PhysicalCalibrationFactorizationChecker public

record Candidate256PhysicalCalibrationExternalReceipt : Setω where
  field
    calibrationAuthority :
      Gate.Candidate256PhysicalCalibrationAuthorityToken

    physicalUnitCarrier : Set

    physicalDimensionVector :
      Candidate256PhysicalCalibrationDimensionVector

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
    physicalDimensionVectorLabel : String
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
  missingExternalPhysicalDimensionVector :
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

data W4PhysicalCalibrationExternalReceiptQueueItem : Set where
  awaitingAcceptedDYLuminosityConventionAuthority :
    W4PhysicalCalibrationExternalReceiptQueueItem
  awaitingW4ZAdequacy :
    W4PhysicalCalibrationExternalReceiptQueueItem
  awaitingCandidate256PhysicalCalibrationExternalReceipt :
    W4PhysicalCalibrationExternalReceiptQueueItem

canonicalW4PhysicalCalibrationExternalReceiptQueue :
  List W4PhysicalCalibrationExternalReceiptQueueItem
canonicalW4PhysicalCalibrationExternalReceiptQueue =
  awaitingAcceptedDYLuminosityConventionAuthority
  ∷ awaitingW4ZAdequacy
  ∷ awaitingCandidate256PhysicalCalibrationExternalReceipt
  ∷ []

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

candidate256PhysicalCalibrationExternalReceiptImpossibleWithoutExternalAuthority :
  Candidate256PhysicalCalibrationExternalReceipt →
  ⊥
candidate256PhysicalCalibrationExternalReceiptImpossibleWithoutExternalAuthority =
  candidate256PhysicalCalibrationExternalReceiptImpossibleHere

canonicalCandidate256PhysicalCalibrationExternalBlockedFields :
  List Candidate256PhysicalCalibrationExternalBlockedField
canonicalCandidate256PhysicalCalibrationExternalBlockedFields =
  missingExternalCalibrationAuthorityToken
  ∷ missingExternalPhysicalUnitCarrier
  ∷ missingExternalPhysicalDimensionVector
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

    downstreamReceiptQueue :
      List W4PhysicalCalibrationExternalReceiptQueueItem

    downstreamReceiptQueueName :
      String

    requiredExternalReceipt : String
    requiredAuthorityArtifact : String
    authorityBoundary : String
    calibrationBoundary : String
    dimensionVectorBoundary : String
    factorizationBoundary : String
    dimensionalBoundary : String
    downstreamPhysicalBoundary : String

    noAuthorityConstructedHere :
      List String

    legitimateAuthorityArtifactBoundary :
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
    ; downstreamReceiptQueue =
        canonicalW4PhysicalCalibrationExternalReceiptQueue
    ; downstreamReceiptQueueName =
        "AcceptedDYLuminosityConventionAuthority -> W4ZAdequacy -> Candidate256PhysicalCalibrationExternalReceipt"
    ; requiredExternalReceipt =
        "after AcceptedDYLuminosityConventionAuthority and W4ZAdequacy, provide an external receipt carrying authority, units, calibration, factorization, and dimensional preservation"
    ; requiredAuthorityArtifact =
        "provide an actual external artifact that inhabits Candidate256PhysicalCalibrationAuthorityToken outside this constructorless repo boundary"
    ; authorityBoundary =
        "Candidate256PhysicalCalibrationAuthorityToken has no constructor in the current repo"
    ; calibrationBoundary =
        "physical unit carrier, Nat-to-unit calibration map, and calibrated quotient scale map remain external obligations"
    ; dimensionVectorBoundary =
        "a physical dimension vector must be supplied as structured SI-base exponents before unit calibration can be consumed"
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
    ; legitimateAuthorityArtifactBoundary =
        "A legitimate Candidate256PhysicalCalibrationExternalReceipt must carry an already-inhabited Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "Local diagnostics, HEPData anchor names, Z-peak shape fits, CT18 packet probes, labels, and prose provenance do not inhabit that token"
        ∷ "The receipt boundary is intentionally downstream of AcceptedDYLuminosityConventionAuthority and W4ZAdequacy: it needs external physical-unit authority plus calibration and dimensional-preservation terms"
        ∷ "Without that authority artifact, this module exposes only the request shape and the impossibility eliminator"
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
        candidate256PhysicalCalibrationExternalReceiptImpossibleWithoutExternalAuthority
    }

record Candidate256PhysicalCalibrationGateReceiptWiringLedger : Setω where
  field
    currentStatus :
      Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    downstreamReceiptQueue :
      List W4PhysicalCalibrationExternalReceiptQueueItem

    downstreamReceiptQueueIsCanonical :
      downstreamReceiptQueue
      ≡
      canonicalW4PhysicalCalibrationExternalReceiptQueue

    blockedExternalFields :
      List Candidate256PhysicalCalibrationExternalBlockedField

    blockedExternalFieldsAreCanonical :
      blockedExternalFields
      ≡
      canonicalCandidate256PhysicalCalibrationExternalBlockedFields

    receiptImpossibleWithoutExternalAuthority :
      Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

    acceptedAuthorityTokenLocallyConstructed :
      Bool

    acceptedAuthorityTokenLocallyConstructedIsFalse :
      acceptedAuthorityTokenLocallyConstructed ≡ false

    gateReceiptWired :
      Bool

    gateReceiptWiredIsTrue :
      gateReceiptWired ≡ true

    physicalCalibrationPromoted :
      Bool

    physicalCalibrationPromotedIsFalse :
      physicalCalibrationPromoted ≡ false

    wiringBoundary :
      List String

open Candidate256PhysicalCalibrationGateReceiptWiringLedger public

canonicalCandidate256PhysicalCalibrationGateReceiptWiringLedger :
  Candidate256PhysicalCalibrationGateReceiptWiringLedger
canonicalCandidate256PhysicalCalibrationGateReceiptWiringLedger =
  record
    { currentStatus =
        canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; downstreamReceiptQueue =
        canonicalW4PhysicalCalibrationExternalReceiptQueue
    ; downstreamReceiptQueueIsCanonical =
        refl
    ; blockedExternalFields =
        canonicalCandidate256PhysicalCalibrationExternalBlockedFields
    ; blockedExternalFieldsAreCanonical =
        refl
    ; receiptImpossibleWithoutExternalAuthority =
        candidate256PhysicalCalibrationExternalReceiptImpossibleWithoutExternalAuthority
    ; acceptedAuthorityTokenLocallyConstructed =
        false
    ; acceptedAuthorityTokenLocallyConstructedIsFalse =
        refl
    ; gateReceiptWired =
        true
    ; gateReceiptWiredIsTrue =
        refl
    ; physicalCalibrationPromoted =
        false
    ; physicalCalibrationPromotedIsFalse =
        refl
    ; wiringBoundary =
        "Gate receipt wiring is recorded from AcceptedDYLuminosityConventionAuthority through W4ZAdequacy to Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "The canonical blocked fields remain authority, unit carrier, dimension vector, Nat-to-unit map, calibrated quotient map, factorization, and dimensional preservation"
        ∷ "The receipt eliminator still proves Candidate256PhysicalCalibrationExternalReceipt is impossible without an external authority token"
        ∷ "No local accepted authority token or physical calibration promotion is constructed"
        ∷ []
    }
