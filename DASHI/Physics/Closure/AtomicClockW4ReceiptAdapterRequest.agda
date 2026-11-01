module DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge as Bridge
import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as External
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptRequestPack as Request
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Surrogate

------------------------------------------------------------------------
-- Atomic-clock W4 receipt adapter request.
--
-- This module maps the checked atomic-clock SI-second bridge onto the exact
-- Candidate256PhysicalCalibrationExternalReceipt field surface.  It is still
-- only a request/adapter: the calibrationAuthority field is an external
-- obligation because Candidate256PhysicalCalibrationAuthorityToken is
-- constructorless in this repo.

candidate256PhysicalCalibrationExternalReceiptTargetPath : String
candidate256PhysicalCalibrationExternalReceiptTargetPath =
  "DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation.Candidate256PhysicalCalibrationExternalReceipt"

constructsCandidate256PhysicalCalibrationExternalReceipt : Bool
constructsCandidate256PhysicalCalibrationExternalReceipt =
  false

constructsCandidate256PhysicalCalibrationExternalReceiptIsFalse :
  constructsCandidate256PhysicalCalibrationExternalReceipt ≡ false
constructsCandidate256PhysicalCalibrationExternalReceiptIsFalse =
  refl

siVectorToCandidate256DimensionVector :
  Bridge.SIBaseDimensionVector →
  External.Candidate256PhysicalCalibrationDimensionVector
siVectorToCandidate256DimensionVector vector =
  record
    { lengthPositiveExponent =
        Bridge.SIExponent.positive
          (Bridge.SIBaseDimensionVector.length vector)
    ; lengthNegativeExponent =
        Bridge.SIExponent.negative
          (Bridge.SIBaseDimensionVector.length vector)
    ; massPositiveExponent =
        Bridge.SIExponent.positive
          (Bridge.SIBaseDimensionVector.mass vector)
    ; massNegativeExponent =
        Bridge.SIExponent.negative
          (Bridge.SIBaseDimensionVector.mass vector)
    ; timePositiveExponent =
        Bridge.SIExponent.positive
          (Bridge.SIBaseDimensionVector.time vector)
    ; timeNegativeExponent =
        Bridge.SIExponent.negative
          (Bridge.SIBaseDimensionVector.time vector)
    ; electricCurrentPositiveExponent =
        Bridge.SIExponent.positive
          (Bridge.SIBaseDimensionVector.current vector)
    ; electricCurrentNegativeExponent =
        Bridge.SIExponent.negative
          (Bridge.SIBaseDimensionVector.current vector)
    ; thermodynamicTemperaturePositiveExponent =
        Bridge.SIExponent.positive
          (Bridge.SIBaseDimensionVector.temperature vector)
    ; thermodynamicTemperatureNegativeExponent =
        Bridge.SIExponent.negative
          (Bridge.SIBaseDimensionVector.temperature vector)
    ; amountOfSubstancePositiveExponent =
        Bridge.SIExponent.positive
          (Bridge.SIBaseDimensionVector.amount vector)
    ; amountOfSubstanceNegativeExponent =
        Bridge.SIExponent.negative
          (Bridge.SIBaseDimensionVector.amount vector)
    ; luminousIntensityPositiveExponent =
        Bridge.SIExponent.positive
          (Bridge.SIBaseDimensionVector.luminousIntensity vector)
    ; luminousIntensityNegativeExponent =
        Bridge.SIExponent.negative
          (Bridge.SIBaseDimensionVector.luminousIntensity vector)
    }

atomicClockCandidate256PhysicalDimensionVector :
  External.Candidate256PhysicalCalibrationDimensionVector
atomicClockCandidate256PhysicalDimensionVector =
  siVectorToCandidate256DimensionVector Bridge.siSecondDimension

data Candidate256ExternalReceiptFieldCoverage : Set where
  coversCalibrationAuthority :
    Candidate256ExternalReceiptFieldCoverage
  coversPhysicalUnitCarrier :
    Candidate256ExternalReceiptFieldCoverage
  coversPhysicalDimensionVector :
    Candidate256ExternalReceiptFieldCoverage
  coversNatToUnitCalibrationMap :
    Candidate256ExternalReceiptFieldCoverage
  coversCalibratedQuotientScaleMap :
    Candidate256ExternalReceiptFieldCoverage
  coversFactorizationLaw :
    Candidate256ExternalReceiptFieldCoverage
  coversDimensionalPreservationLaw :
    Candidate256ExternalReceiptFieldCoverage
  coversDimensionalPreservationAtWitness :
    Candidate256ExternalReceiptFieldCoverage
  coversLabels :
    Candidate256ExternalReceiptFieldCoverage

atomicClockAdapterCoverage :
  List Candidate256ExternalReceiptFieldCoverage
atomicClockAdapterCoverage =
  coversCalibrationAuthority
  ∷ coversPhysicalUnitCarrier
  ∷ coversPhysicalDimensionVector
  ∷ coversNatToUnitCalibrationMap
  ∷ coversCalibratedQuotientScaleMap
  ∷ coversFactorizationLaw
  ∷ coversDimensionalPreservationLaw
  ∷ coversDimensionalPreservationAtWitness
  ∷ coversLabels
  ∷ []

record Candidate256ExternalReceiptFieldSourceRef : Set where
  field
    receiptField : String
    sourceRef : String

open Candidate256ExternalReceiptFieldSourceRef public

atomicClockAdapterFieldSourceRefs :
  List Candidate256ExternalReceiptFieldSourceRef
atomicClockAdapterFieldSourceRefs =
  record
    { receiptField = "calibrationAuthority"
    ; sourceRef =
        "External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.requiredAuthorityArtifact"
    }
  ∷ record
    { receiptField = "physicalUnitCarrier"
    ; sourceRef =
        "Bridge.AtomicClockSISecondCalibrationBridge.physicalUnitCarrier"
    }
  ∷ record
    { receiptField = "physicalDimensionVector"
    ; sourceRef =
        "Bridge.AtomicClockSISecondCalibrationBridge.secondDimension"
    }
  ∷ record
    { receiptField = "natToUnitCalibrationMap"
    ; sourceRef =
        "Bridge.AtomicClockSISecondCalibrationBridge.natToUnitCalibrationRoute"
    }
  ∷ record
    { receiptField = "calibratedQuotientScaleMap"
    ; sourceRef =
        "Bridge.AtomicClockSISecondCalibrationBridge.quotientScaleRoute"
    }
  ∷ record
    { receiptField = "calibratedScaleMapFactorsThroughNat"
    ; sourceRef =
        "Bridge.AtomicClockSISecondCalibrationBridge.factorizationLawRequest"
    }
  ∷ record
    { receiptField = "dimensionalPreservationLaw"
    ; sourceRef =
        "Bridge.AtomicClockSISecondCalibrationBridge.dimensionalPreservationRequest"
    }
  ∷ record
    { receiptField = "dimensionalPreservationAtWitness"
    ; sourceRef =
        "Bridge.AtomicClockSISecondCalibrationBridge.dimensionalPreservationRequested"
    }
  ∷ record
    { receiptField = "labels"
    ; sourceRef =
        "AtomicClockW4ReceiptAdapterRequest canonical label fields"
    }
  ∷ []

record AtomicClockW4ReceiptAdapterRequest : Setω where
  field
    sourceBridge :
      Bridge.AtomicClockSISecondCalibrationBridge

    currentStatus :
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    requestPack :
      Request.W4PhysicalCalibrationExternalReceiptRequestPack

    fieldCoverage :
      List Candidate256ExternalReceiptFieldCoverage

    fieldSourceRefs :
      List Candidate256ExternalReceiptFieldSourceRef

    calibrationAuthority :
      String

    calibrationAuthoritySourceRef :
      String

    physicalUnitCarrier :
      Set

    physicalUnitCarrierMatchesBridge :
      physicalUnitCarrier
      ≡
      Bridge.AtomicClockSISecondCalibrationBridge.physicalUnitCarrier
        sourceBridge

    physicalDimensionVector :
      External.Candidate256PhysicalCalibrationDimensionVector

    physicalDimensionVectorSourceRef :
      String

    natToUnitCalibrationMap :
      Nat →
      physicalUnitCarrier

    natToUnitCalibrationMapSourceRef :
      String

    calibratedQuotientScaleMap :
      Surrogate.Candidate256QuotientClass →
      physicalUnitCarrier

    calibratedQuotientScaleMapSourceRef :
      String

    calibratedScaleMapFactorsThroughNat :
      (q : Surrogate.Candidate256QuotientClass) →
      calibratedQuotientScaleMap q
      ≡
      natToUnitCalibrationMap (Surrogate.candidate256SurrogateScale q)

    factorizationSourceRef :
      String

    dimensionalPreservationLaw :
      Handoff.QuotientLawAtWitness
        Next.canonicalCandidate256QuotientLaw →
      Set

    dimensionalPreservationLawSourceRef :
      String

    dimensionalPreservationAtWitness :
      (law :
        Handoff.QuotientLawAtWitness
          Next.canonicalCandidate256QuotientLaw) →
      dimensionalPreservationLaw law

    dimensionalPreservationAtWitnessSourceRef :
      String

    physicalUnitCarrierLabel : String
    physicalDimensionVectorLabel : String
    natToUnitCalibrationMapLabel : String
    calibratedQuotientScaleMapLabel : String
    factorizationLabel : String
    dimensionalPreservationLabel : String

    impossibleAuthorityHere :
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.impossibleWithoutExternalAuthority
        currentStatus
      ≡
      External.candidate256PhysicalCalibrationAuthorityTokenImpossibleHere

    impossibleReceiptHere :
      External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

    constructsCandidate256ExternalReceipt :
      Bool

    constructsCandidate256ExternalReceiptIsFalse :
      constructsCandidate256ExternalReceipt ≡ false

    promotesW4PhysicalCalibration :
      Bool

    promotesW4PhysicalCalibrationIsFalse :
      promotesW4PhysicalCalibration ≡ false

    adapterBoundary :
      List String

open AtomicClockW4ReceiptAdapterRequest public

canonicalAtomicClockW4ReceiptAdapterRequest :
  AtomicClockW4ReceiptAdapterRequest
canonicalAtomicClockW4ReceiptAdapterRequest =
  record
    { sourceBridge =
        Bridge.canonicalAtomicClockSISecondCalibrationBridge
    ; currentStatus =
        External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; requestPack =
        Request.canonicalW4PhysicalCalibrationExternalReceiptRequestPack
    ; fieldCoverage =
        atomicClockAdapterCoverage
    ; fieldSourceRefs =
        atomicClockAdapterFieldSourceRefs
    ; calibrationAuthority =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.requiredAuthorityArtifact
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; calibrationAuthoritySourceRef =
        "External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.requiredAuthorityArtifact"
    ; physicalUnitCarrier =
        Bridge.AtomicClockSISecondCalibrationBridge.physicalUnitCarrier
          Bridge.canonicalAtomicClockSISecondCalibrationBridge
    ; physicalUnitCarrierMatchesBridge =
        refl
    ; physicalDimensionVector =
        siVectorToCandidate256DimensionVector
          (Bridge.AtomicClockSISecondCalibrationBridge.secondDimension
            Bridge.canonicalAtomicClockSISecondCalibrationBridge)
    ; physicalDimensionVectorSourceRef =
        "Bridge.canonicalAtomicClockSISecondCalibrationBridge.secondDimension"
    ; natToUnitCalibrationMap =
        Bridge.AtomicClockSISecondCalibrationBridge.natToUnitCalibrationRoute
          Bridge.canonicalAtomicClockSISecondCalibrationBridge
    ; natToUnitCalibrationMapSourceRef =
        "Bridge.canonicalAtomicClockSISecondCalibrationBridge.natToUnitCalibrationRoute"
    ; calibratedQuotientScaleMap =
        Bridge.AtomicClockSISecondCalibrationBridge.quotientScaleRoute
          Bridge.canonicalAtomicClockSISecondCalibrationBridge
    ; calibratedQuotientScaleMapSourceRef =
        "Bridge.canonicalAtomicClockSISecondCalibrationBridge.quotientScaleRoute"
    ; calibratedScaleMapFactorsThroughNat =
        Bridge.AtomicClockSISecondCalibrationBridge.factorizationLawRequest
          Bridge.canonicalAtomicClockSISecondCalibrationBridge
    ; factorizationSourceRef =
        "Bridge.canonicalAtomicClockSISecondCalibrationBridge.factorizationLawRequest"
    ; dimensionalPreservationLaw =
        Bridge.AtomicClockSISecondCalibrationBridge.dimensionalPreservationRequest
          Bridge.canonicalAtomicClockSISecondCalibrationBridge
    ; dimensionalPreservationLawSourceRef =
        "Bridge.canonicalAtomicClockSISecondCalibrationBridge.dimensionalPreservationRequest"
    ; dimensionalPreservationAtWitness =
        Bridge.AtomicClockSISecondCalibrationBridge.dimensionalPreservationRequested
          Bridge.canonicalAtomicClockSISecondCalibrationBridge
    ; dimensionalPreservationAtWitnessSourceRef =
        "Bridge.canonicalAtomicClockSISecondCalibrationBridge.dimensionalPreservationRequested"
    ; physicalUnitCarrierLabel =
        "SI time/frequency carrier from AtomicClockSISecondCalibrationBridge"
    ; physicalDimensionVectorLabel =
        "SI second dimension vector mapped into Candidate256 physical calibration exponents"
    ; natToUnitCalibrationMapLabel =
        "Nat -> SI second route from the atomic-clock bridge"
    ; calibratedQuotientScaleMapLabel =
        "Candidate256 quotient class -> SI second route from the atomic-clock bridge"
    ; factorizationLabel =
        "atomic-clock quotient route factors through candidate256SurrogateScale"
    ; dimensionalPreservationLabel =
        "SI second dimensional preservation request at Candidate256 quotient-law witness"
    ; impossibleAuthorityHere =
        refl
    ; impossibleReceiptHere =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.impossibleReceiptWithoutExternalAuthority
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; constructsCandidate256ExternalReceipt =
        false
    ; constructsCandidate256ExternalReceiptIsFalse =
        refl
    ; promotesW4PhysicalCalibration =
        false
    ; promotesW4PhysicalCalibrationIsFalse =
        refl
    ; adapterBoundary =
        "The adapter maps bridge fields onto the Candidate256PhysicalCalibrationExternalReceipt field surface"
        ∷ "calibrationAuthority remains an external authority-token requirement, not a locally constructed token"
        ∷ "physicalUnitCarrier, dimension vector, Nat map, quotient map, factorization, dimensional law, witness, and labels are surfaced from the bridge"
        ∷ "The current-status impossible receipt function is reused as the fail-closed eliminator"
        ∷ "No Candidate256PhysicalCalibrationExternalReceipt and no W4 physical-calibration promotion are constructed"
        ∷ []
    }

canonicalAtomicClockAdapterCoversAllReceiptFields :
  AtomicClockW4ReceiptAdapterRequest.fieldCoverage
    canonicalAtomicClockW4ReceiptAdapterRequest
  ≡
  atomicClockAdapterCoverage
canonicalAtomicClockAdapterCoversAllReceiptFields =
  refl

canonicalAtomicClockAdapterPhysicalUnitCarrierMatchesBridge :
  AtomicClockW4ReceiptAdapterRequest.physicalUnitCarrier
    canonicalAtomicClockW4ReceiptAdapterRequest
  ≡
  Bridge.AtomicClockSISecondCalibrationBridge.physicalUnitCarrier
    Bridge.canonicalAtomicClockSISecondCalibrationBridge
canonicalAtomicClockAdapterPhysicalUnitCarrierMatchesBridge =
  refl

canonicalAtomicClockAdapterNatToUnitMapMatchesBridge :
  AtomicClockW4ReceiptAdapterRequest.natToUnitCalibrationMap
    canonicalAtomicClockW4ReceiptAdapterRequest
  ≡
  Bridge.AtomicClockSISecondCalibrationBridge.natToUnitCalibrationRoute
    Bridge.canonicalAtomicClockSISecondCalibrationBridge
canonicalAtomicClockAdapterNatToUnitMapMatchesBridge =
  refl

canonicalAtomicClockAdapterQuotientMapMatchesBridge :
  AtomicClockW4ReceiptAdapterRequest.calibratedQuotientScaleMap
    canonicalAtomicClockW4ReceiptAdapterRequest
  ≡
  Bridge.AtomicClockSISecondCalibrationBridge.quotientScaleRoute
    Bridge.canonicalAtomicClockSISecondCalibrationBridge
canonicalAtomicClockAdapterQuotientMapMatchesBridge =
  refl

canonicalAtomicClockAdapterFactorizationMatchesBridge :
  (q : Surrogate.Candidate256QuotientClass) →
  AtomicClockW4ReceiptAdapterRequest.calibratedQuotientScaleMap
    canonicalAtomicClockW4ReceiptAdapterRequest
    q
  ≡
  AtomicClockW4ReceiptAdapterRequest.natToUnitCalibrationMap
    canonicalAtomicClockW4ReceiptAdapterRequest
    (Surrogate.candidate256SurrogateScale q)
canonicalAtomicClockAdapterFactorizationMatchesBridge =
  AtomicClockW4ReceiptAdapterRequest.calibratedScaleMapFactorsThroughNat
    canonicalAtomicClockW4ReceiptAdapterRequest

canonicalAtomicClockAdapterDimensionalPreservationAtWitness :
  (law :
    Handoff.QuotientLawAtWitness
      Next.canonicalCandidate256QuotientLaw) →
  AtomicClockW4ReceiptAdapterRequest.dimensionalPreservationLaw
    canonicalAtomicClockW4ReceiptAdapterRequest
    law
canonicalAtomicClockAdapterDimensionalPreservationAtWitness =
  AtomicClockW4ReceiptAdapterRequest.dimensionalPreservationAtWitness
    canonicalAtomicClockW4ReceiptAdapterRequest

canonicalAtomicClockAdapterReceiptImpossible :
  External.Candidate256PhysicalCalibrationExternalReceipt →
  ⊥
canonicalAtomicClockAdapterReceiptImpossible =
  AtomicClockW4ReceiptAdapterRequest.impossibleReceiptHere
    canonicalAtomicClockW4ReceiptAdapterRequest

canonicalAtomicClockAdapterDoesNotConstructReceipt :
  AtomicClockW4ReceiptAdapterRequest.constructsCandidate256ExternalReceipt
    canonicalAtomicClockW4ReceiptAdapterRequest
  ≡
  false
canonicalAtomicClockAdapterDoesNotConstructReceipt =
  refl

canonicalAtomicClockAdapterDoesNotPromoteW4 :
  AtomicClockW4ReceiptAdapterRequest.promotesW4PhysicalCalibration
    canonicalAtomicClockW4ReceiptAdapterRequest
  ≡
  false
canonicalAtomicClockAdapterDoesNotPromoteW4 =
  refl
