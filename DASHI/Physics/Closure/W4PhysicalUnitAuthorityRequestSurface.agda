module DASHI.Physics.Closure.W4PhysicalUnitAuthorityRequestSurface where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.TSFVCandidate256CalibrationLawDiagnostic as TSFV
import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as External
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptRequestPack as Pack
import DASHI.Physics.Closure.W4PhysicalCalibrationGate as Gate
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next

------------------------------------------------------------------------
-- W4 physical-unit authority request surface.
--
-- The TSFV trit calibration law is internally constructed in the diagnostic
-- lane.  This module requests only the external physical-unit authority
-- needed before that internal law can be consumed by W4.  It constructs no
-- Candidate256PhysicalCalibrationAuthorityToken and no external receipt.

data W4PhysicalUnitAuthorityRequestStatus : Set where
  internalTSFVTritLawAvailableAwaitingPhysicalUnitAuthority :
    W4PhysicalUnitAuthorityRequestStatus

data W4PhysicalUnitAuthorityMissingField : Set where
  missingExternalPhysicalUnitCarrier :
    W4PhysicalUnitAuthorityMissingField
  missingExternalBaseUnit :
    W4PhysicalUnitAuthorityMissingField
  missingExternalDimensionCarrier :
    W4PhysicalUnitAuthorityMissingField
  missingExternalDimensionOfUnit :
    W4PhysicalUnitAuthorityMissingField
  missingExternalConversionTarget :
    W4PhysicalUnitAuthorityMissingField
  missingExternalConversionLaw :
    W4PhysicalUnitAuthorityMissingField
  missingExternalDimensionalPreservationStatement :
    W4PhysicalUnitAuthorityMissingField
  missingCandidate256TSFVBindingLaw :
    W4PhysicalUnitAuthorityMissingField
  missingCandidate256PhysicalCalibrationAuthorityToken :
    W4PhysicalUnitAuthorityMissingField
  missingCandidate256PhysicalCalibrationExternalReceipt :
    W4PhysicalUnitAuthorityMissingField

data W4TSFVChemistryWitnessSelectionStatus : Set where
  witnessSelectionOpenUntilRchemRelationFixed :
    W4TSFVChemistryWitnessSelectionStatus
  providerChemistryLawReceiptRequiredBeforeSelection :
    W4TSFVChemistryWitnessSelectionStatus

data W4TSFVChemistryReceiptMissingField : Set where
  missingProviderRchemRelation :
    W4TSFVChemistryReceiptMissingField
  missingProviderWitnessSelectionRule :
    W4TSFVChemistryReceiptMissingField
  missingProviderChemistryLawReceipt :
    W4TSFVChemistryReceiptMissingField
  missingProviderBaseUnitAuthorityBinding :
    W4TSFVChemistryReceiptMissingField
  missingCandidate256PhysicalCalibrationAuthorityTokenForChemistry :
    W4TSFVChemistryReceiptMissingField

canonicalW4TSFVChemistryReceiptMissingFields :
  List W4TSFVChemistryReceiptMissingField
canonicalW4TSFVChemistryReceiptMissingFields =
  missingProviderWitnessSelectionRule
  ∷ missingProviderChemistryLawReceipt
  ∷ missingProviderBaseUnitAuthorityBinding
  ∷ missingCandidate256PhysicalCalibrationAuthorityTokenForChemistry
  ∷ []

canonicalW4PhysicalUnitAuthorityMissingFields :
  List W4PhysicalUnitAuthorityMissingField
canonicalW4PhysicalUnitAuthorityMissingFields =
  missingExternalPhysicalUnitCarrier
  ∷ missingExternalBaseUnit
  ∷ missingExternalDimensionCarrier
  ∷ missingExternalDimensionOfUnit
  ∷ missingExternalConversionTarget
  ∷ missingExternalConversionLaw
  ∷ missingExternalDimensionalPreservationStatement
  ∷ missingCandidate256TSFVBindingLaw
  ∷ missingCandidate256PhysicalCalibrationAuthorityToken
  ∷ missingCandidate256PhysicalCalibrationExternalReceipt
  ∷ []

record W4PhysicalUnitAuthorityProviderRequest : Setω where
  field
    status :
      W4PhysicalUnitAuthorityRequestStatus

    internalTSFVTritCalibrationLaw :
      TSFV.TSFVTritCalibrationLaw

    externalReceiptRequestPack :
      Pack.W4PhysicalCalibrationExternalReceiptRequestPack

    externalReceiptCurrentStatus :
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    exactAuthorityTokenName :
      String

    exactExternalReceiptName :
      String

    requiredBaseUnit :
      String

    requiredProviderFields :
      List String

    exactMissingFields :
      List W4PhysicalUnitAuthorityMissingField

    acceptedResponseMustSupply :
      List String

    candidate256TSFVBindingRequirements :
      List String

    rejectedSubstitutes :
      List String

    nonPromotionBoundary :
      List String

    constructsCandidate256PhysicalCalibrationAuthorityToken :
      Bool

    constructsCandidate256PhysicalCalibrationExternalReceipt :
      Bool

    promotesW4 :
      Bool

    impossibleAuthorityHere :
      Gate.Candidate256PhysicalCalibrationAuthorityToken →
      ⊥

    impossibleReceiptHere :
      External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

record W4TSFVPhysicalUnitAuthorityBridge : Setω where
  field
    request :
      W4PhysicalUnitAuthorityProviderRequest

    tsfvLaw :
      TSFV.TSFVTritCalibrationLaw

    tsfvBaseUnit :
      TSFV.TSFVTritCalibrationLaw.PhysicalUnitCarrier tsfvLaw

    w4RequiredBaseUnitWitness :
      TSFV.TSFVTritCalibrationLaw.PhysicalUnitCarrier tsfvLaw

    baseUnitIsRequiredBaseUnit :
      tsfvBaseUnit ≡ w4RequiredBaseUnitWitness

    w4RequiredBaseUnit :
      String

    sharedProviderObligationName :
      String

    equivalenceStatement :
      String

    providerMustSupply :
      List String

    bridgeRejectedSubstitutes :
      List String

    nonPromotionBoundary :
      List String

    constructsCandidate256PhysicalCalibrationAuthorityToken :
      Bool

    constructsCandidate256PhysicalCalibrationExternalReceipt :
      Bool

    promotesW4 :
      Bool

record W4TSFVChemistryLawReceiptRequest : Setω where
  field
    unitAuthorityBridge :
      W4TSFVPhysicalUnitAuthorityBridge

    internalTSFVTritCalibrationLaw :
      TSFV.TSFVTritCalibrationLaw

    tsfvBaseUnit :
      TSFV.TSFVTritCalibrationLaw.PhysicalUnitCarrier
        internalTSFVTritCalibrationLaw

    requiredBaseUnit :
      TSFV.TSFVTritCalibrationLaw.PhysicalUnitCarrier
        internalTSFVTritCalibrationLaw

    baseUnitEqualsRequiredBaseUnit :
      tsfvBaseUnit ≡ requiredBaseUnit

    rChemObligation :
      Handoff.QuotientLawAtWitness
        Next.canonicalCandidate256QuotientLaw →
      Set

    witnessSelectionStatus :
      W4TSFVChemistryWitnessSelectionStatus

    missingReceiptFields :
      List W4TSFVChemistryReceiptMissingField

    requestBoundary :
      List String

    providerMustSupply :
      List String

    constructsProviderChemistryLawReceipt :
      Bool

    constructsCandidate256PhysicalCalibrationAuthorityToken :
      Bool

    constructsCandidate256PhysicalCalibrationExternalReceipt :
      Bool

    promotesW4 :
      Bool

canonicalW4PhysicalUnitAuthorityProviderRequest :
  W4PhysicalUnitAuthorityProviderRequest
canonicalW4PhysicalUnitAuthorityProviderRequest =
  record
    { status =
        internalTSFVTritLawAvailableAwaitingPhysicalUnitAuthority
    ; internalTSFVTritCalibrationLaw =
        TSFV.candidate256InternalTritCalibrationLaw
    ; externalReceiptRequestPack =
        Pack.canonicalW4PhysicalCalibrationExternalReceiptRequestPack
    ; externalReceiptCurrentStatus =
        External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; exactAuthorityTokenName =
        "DASHI.Physics.Closure.W4PhysicalCalibrationGate.Candidate256PhysicalCalibrationAuthorityToken"
    ; exactExternalReceiptName =
        "DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation.Candidate256PhysicalCalibrationExternalReceipt"
    ; requiredBaseUnit =
        "same external provider obligation as TSFV.TSFVTritCalibrationLaw.baseUnit; not satisfied by the internal diagnostic base unit alone"
    ; requiredProviderFields =
        "PhysicalUnitCarrier : Set"
        ∷ "baseUnit : PhysicalUnitCarrier"
        ∷ "DimensionCarrier : Set"
        ∷ "dimensionOfUnit : PhysicalUnitCarrier -> DimensionCarrier"
        ∷ "conversionTarget : SI-or-natural-unit target named by the provider"
        ∷ "conversionLaw : baseUnit and calibrated units convert to the named target"
        ∷ "dimensionalPreservationStatement : calibrated Candidate256/TSFV units preserve the declared dimension"
        ∷ "natToUnitCalibrationMap : Nat -> PhysicalUnitCarrier"
        ∷ "calibratedQuotientScaleMap : Candidate256QuotientClass -> PhysicalUnitCarrier"
        ∷ "Candidate256TSFVBindingLaw : calibratedQuotientScaleMap agrees with the internal TSFV trit calibration law"
        ∷ "candidate256PhysicalCalibrationAuthorityToken : external artifact inhabiting the constructorless token boundary"
        ∷ "provider citation, provenance, validation payload, and authority boundary"
        ∷ []
    ; exactMissingFields =
        canonicalW4PhysicalUnitAuthorityMissingFields
    ; acceptedResponseMustSupply =
        "a non-Nat physical unit carrier with an explicit baseUnit"
        ∷ "a dimension carrier and dimensionOfUnit map"
        ∷ "a conversion law to SI units or to an explicitly named natural-unit convention"
        ∷ "a dimensional preservation statement for the calibrated Candidate256/TSFV map"
        ∷ "a binding law from TSFV.candidate256InternalTritCalibrationLaw to the W4 calibrated quotient scale map"
        ∷ "an external Candidate256PhysicalCalibrationAuthorityToken artifact"
        ∷ "a payload sufficient to inhabit Candidate256PhysicalCalibrationExternalReceipt outside this request surface"
        ∷ []
    ; candidate256TSFVBindingRequirements =
        "The internal TSFV trit law may be used only as dimensionless structure before authority intake"
        ∷ "The provider must state how its natToUnitCalibrationMap consumes TSFV trit depth or the existing Candidate256 surrogate scale"
        ∷ "The provider must prove calibratedQuotientScaleMap q matches the chosen unit calibration of the internal Candidate256/TSFV value"
        ∷ "The provider must preserve Candidate256 quotient-law dimensional meaning at every QuotientLawAtWitness canonicalCandidate256QuotientLaw"
        ∷ "If the provider uses the existing W4 receipt shape, it must also satisfy calibratedScaleMapFactorsThroughNat"
        ∷ []
    ; rejectedSubstitutes =
        "TSFV.candidate256InternalTritCalibrationLaw by itself"
        ∷ "TSFVDiagnosticPhysicalUnitCarrier by itself"
        ∷ "the dimensionless Nat surrogate by itself"
        ∷ "labels, comments, citations, or prose dimensional annotations without typed fields"
        ∷ "Drosophila/codon candidate evidence without physical-unit authority"
        ∷ []
    ; nonPromotionBoundary =
        "This request surface does not construct Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "This request surface does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "This request surface does not promote TSFVDiagnosticPhysicalUnitCarrier to external physical authority"
        ∷ "This request surface does not promote W4, matter, stress-energy, spectra, bonding, or empirical validation"
        ∷ []
    ; constructsCandidate256PhysicalCalibrationAuthorityToken =
        false
    ; constructsCandidate256PhysicalCalibrationExternalReceipt =
        false
    ; promotesW4 =
        false
    ; impossibleAuthorityHere =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.impossibleWithoutExternalAuthority
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; impossibleReceiptHere =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.impossibleReceiptWithoutExternalAuthority
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    }

canonicalW4TSFVPhysicalUnitAuthorityBridge :
  W4TSFVPhysicalUnitAuthorityBridge
canonicalW4TSFVPhysicalUnitAuthorityBridge =
  record
    { request =
        canonicalW4PhysicalUnitAuthorityProviderRequest
    ; tsfvLaw =
        TSFV.candidate256InternalTritCalibrationLaw
    ; tsfvBaseUnit =
        TSFV.TSFVTritCalibrationLaw.baseUnit
          TSFV.candidate256InternalTritCalibrationLaw
    ; w4RequiredBaseUnitWitness =
        TSFV.TSFVTritCalibrationLaw.baseUnit
          TSFV.candidate256InternalTritCalibrationLaw
    ; baseUnitIsRequiredBaseUnit =
        refl
    ; w4RequiredBaseUnit =
        W4PhysicalUnitAuthorityProviderRequest.requiredBaseUnit
          canonicalW4PhysicalUnitAuthorityProviderRequest
    ; sharedProviderObligationName =
        "TSFV baseUnit == W4 requiredBaseUnit"
    ; equivalenceStatement =
        "The TSFV trit calibration baseUnit and the W4 kill-matrix requiredBaseUnit name the same external physical-unit authority obligation, viewed from the chemistry/TSFV law and W4 blocker sides"
    ; providerMustSupply =
        "baseUnit : PhysicalUnitCarrier"
        ∷ "DimensionCarrier : Set"
        ∷ "dimensionOfUnit : PhysicalUnitCarrier -> DimensionCarrier"
        ∷ "conversionLaw : baseUnit and calibrated Candidate256/TSFV units convert to the provider-named target"
        ∷ "dimensionalPreservationStatement : calibrated Candidate256/TSFV units preserve the declared dimension"
        ∷ "authorityCitation : DOI, standard, provider artifact, review record, or equivalent citation"
        ∷ "validationPayload : checksums, provenance, measurement inputs, commands or API calls, timestamps, and review boundary"
        ∷ []
    ; bridgeRejectedSubstitutes =
        "TSFV.TSFVTritCalibrationLaw.baseUnit from the internal diagnostic carrier alone"
        ∷ "W4 requiredBaseUnit as a label without typed carrier, dimension, conversion, preservation, citation, and validation payload"
        ∷ "Candidate256 Nat surrogate scale values without external physical-unit authority"
        ∷ []
    ; nonPromotionBoundary =
        "This bridge only identifies one shared provider obligation"
        ∷ "It does not turn TSFVDiagnosticPhysicalUnitCarrier into an external physical unit carrier"
        ∷ "It does not construct Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "It does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "It does not promote W4, chemistry, spectra, bonding, stress-energy, or empirical validation"
        ∷ []
    ; constructsCandidate256PhysicalCalibrationAuthorityToken =
        false
    ; constructsCandidate256PhysicalCalibrationExternalReceipt =
        false
    ; promotesW4 =
        false
    }

canonicalW4TSFVChemistryLawReceiptRequest :
  W4TSFVChemistryLawReceiptRequest
canonicalW4TSFVChemistryLawReceiptRequest =
  record
    { unitAuthorityBridge =
        canonicalW4TSFVPhysicalUnitAuthorityBridge
    ; internalTSFVTritCalibrationLaw =
        TSFV.candidate256InternalTritCalibrationLaw
    ; tsfvBaseUnit =
        TSFV.TSFVTritCalibrationLaw.baseUnit
          TSFV.candidate256InternalTritCalibrationLaw
    ; requiredBaseUnit =
        TSFV.TSFVTritCalibrationLaw.baseUnit
          TSFV.candidate256InternalTritCalibrationLaw
    ; baseUnitEqualsRequiredBaseUnit =
        refl
    ; rChemObligation =
        TSFV.Candidate256RchemRelationAtWitness
    ; witnessSelectionStatus =
        providerChemistryLawReceiptRequiredBeforeSelection
    ; missingReceiptFields =
        canonicalW4TSFVChemistryReceiptMissingFields
    ; requestBoundary =
        "R-chem is fixed as Candidate256RchemRelationAtWitness: an L_chem witness with TSFV T-invariance and nontrivial positive/T-flipped separation"
        ∷ "Witness selection still requires a provider chemistry-law receipt and external baseUnit authority before it can be consumed"
        ∷ "The requiredBaseUnit witness is definitionally the TSFV trit calibration baseUnit, but this is still the internal diagnostic carrier"
        ∷ "No provider chemistry-law receipt is constructed here"
        ∷ []
    ; providerMustSupply =
        "witness selection rule for Candidate256RchemRelationAtWitness"
        ∷ "chemistry-law receipt or provider artifact validating the selected witnesses"
        ∷ "external physical-unit authority binding the selected R-chem witnesses to the shared baseUnit/requiredBaseUnit obligation"
        ∷ []
    ; constructsProviderChemistryLawReceipt =
        false
    ; constructsCandidate256PhysicalCalibrationAuthorityToken =
        false
    ; constructsCandidate256PhysicalCalibrationExternalReceipt =
        false
    ; promotesW4 =
        false
    }
