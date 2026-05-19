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
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Surrogate

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
  missingProviderBoundBaseUnitCitation :
    W4PhysicalUnitAuthorityMissingField
  missingProviderBoundBaseUnitChecksum :
    W4PhysicalUnitAuthorityMissingField

data W4BaseUnitCandidateRoute : Set where
  protonMassCODATACandidate :
    W4BaseUnitCandidateRoute
  dyConventionNaturalUnitCandidate :
    W4BaseUnitCandidateRoute
  providerSuppliedOtherBaseUnitCandidate :
    W4BaseUnitCandidateRoute

data W4TSFVChemistryWitnessSelectionStatus : Set where
  witnessSelectionOpenUntilRchemRelationFixed :
    W4TSFVChemistryWitnessSelectionStatus
  providerChemistryLawReceiptRequiredBeforeSelection :
    W4TSFVChemistryWitnessSelectionStatus

data W4PhysicalUnitAuthorityProviderReceiptSurfaceStatus : Set where
  providerReceiptSurfaceOnlyAwaitingExternalAuthority :
    W4PhysicalUnitAuthorityProviderReceiptSurfaceStatus

data W4QuotientSensitiveCrossBandWitnessStatus : Set where
  quotientSensitiveWitnessAvailableAtInternalTSFVLevelOnly :
    W4QuotientSensitiveCrossBandWitnessStatus

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
  ∷ missingProviderBoundBaseUnitCitation
  ∷ missingProviderBoundBaseUnitChecksum
  ∷ []

record W4BaseUnitCandidateAuthorityRoute : Set where
  field
    candidateRoute :
      W4BaseUnitCandidateRoute

    candidateRouteName :
      String

    candidateBaseUnitName :
      String

    candidateDimension :
      String

    candidateConversionTarget :
      String

    requiredProviderCitation :
      String

    requiredProviderValidation :
      List String

    acceptedOnlyIfProviderBound :
      List String

    rejectedInterpretations :
      List String

    constructsPhysicalUnitAuthority :
      Bool

    constructsCandidate256PhysicalCalibrationAuthorityToken :
      Bool

    promotesW4 :
      Bool

protonMassCODATACandidateRoute :
  W4BaseUnitCandidateAuthorityRoute
protonMassCODATACandidateRoute =
  record
    { candidateRoute =
        protonMassCODATACandidate
    ; candidateRouteName =
        "proton-mass CODATA/natural-unit candidate route"
    ; candidateBaseUnitName =
        "proton mass energy-equivalent candidate; provider must bind exact value and unit convention"
    ; candidateDimension =
        "mass or energy in an explicitly named natural-unit convention"
    ; candidateConversionTarget =
        "provider-bound SI or natural-unit target; e.g. MeV/c^2, GeV, kg, or c = hbar = 1 convention"
    ; requiredProviderCitation =
        "provider must supply DOI/standard/table/version for the proton mass or replacement base unit; current proton-mass candidate should use CODATA 2022 value 938.27208943(29) MeV, not the stale CODATA 2018 value"
    ; requiredProviderValidation =
        "exact value and uncertainty"
        ∷ "unit convention and conversion target"
        ∷ "checksum or immutable citation for the authority record"
        ∷ "statement that this base unit is admissible for Candidate256/TSFV W4 calibration"
        ∷ "dimensional preservation binding for the calibrated quotient scale map"
        ∷ []
    ; acceptedOnlyIfProviderBound =
        "A proton-mass value is only a candidate until a provider binds the citation, value, uncertainty, unit convention, and conversion law"
        ∷ "The route does not by itself choose proton mass as W4 baseUnit"
        ∷ "The route does not by itself prove Candidate256 physical calibration"
        ∷ []
    ; rejectedInterpretations =
        "proton mass mentioned in prose as a completed authority"
        ∷ "a remembered numeric value without provider checksum or citation"
        ∷ "a base-unit label without DimensionCarrier and conversionLaw"
        ∷ []
    ; constructsPhysicalUnitAuthority =
        false
    ; constructsCandidate256PhysicalCalibrationAuthorityToken =
        false
    ; promotesW4 =
        false
    }

dyConventionNaturalUnitCandidateRoute :
  W4BaseUnitCandidateAuthorityRoute
dyConventionNaturalUnitCandidateRoute =
  record
    { candidateRoute =
        dyConventionNaturalUnitCandidate
    ; candidateRouteName =
        "accepted DY convention natural-unit candidate route"
    ; candidateBaseUnitName =
        "base unit inherited from an accepted DY luminosity/cross-section convention"
    ; candidateDimension =
        "cross-section, energy, luminosity, or natural-unit dimension as declared by the accepted DY provider"
    ; candidateConversionTarget =
        "the conversion target named by AcceptedDYLuminosityConventionAuthorityReceipt"
    ; requiredProviderCitation =
        "provider must supply the accepted DY convention receipt or replacement authority packet"
    ; requiredProviderValidation =
        "luminosity, bin-normalisation, efficiency, acceptance, and systematic-budget provenance"
        ∷ "normalisation-preservation law"
        ∷ "conversion law from DY convention units to Candidate256/TSFV calibrated units"
        ∷ "statement that the selected DY base unit satisfies W4 physical-unit authority"
        ∷ []
    ; acceptedOnlyIfProviderBound =
        "The DY route is only admissible after AcceptedDYLuminosityConventionAuthorityReceipt or replacement authority exists"
        ∷ "It cannot be inferred from the local pressure decomposition tool exiting 45"
        ∷ []
    ; rejectedInterpretations =
        "using a DY paper label without accepted convention fields"
        ∷ "using local HEPData artifacts as physical-unit authority"
        ∷ "using pressure-attribution diagnostics as base-unit authority"
        ∷ []
    ; constructsPhysicalUnitAuthority =
        false
    ; constructsCandidate256PhysicalCalibrationAuthorityToken =
        false
    ; promotesW4 =
        false
    }

providerSuppliedOtherBaseUnitCandidateRoute :
  W4BaseUnitCandidateAuthorityRoute
providerSuppliedOtherBaseUnitCandidateRoute =
  record
    { candidateRoute =
        providerSuppliedOtherBaseUnitCandidate
    ; candidateRouteName =
        "provider-supplied replacement base-unit candidate route"
    ; candidateBaseUnitName =
        "provider-named base unit"
    ; candidateDimension =
        "provider-named dimension carrier"
    ; candidateConversionTarget =
        "provider-named SI or natural-unit conversion target"
    ; requiredProviderCitation =
        "provider must cite and validate the replacement base-unit authority"
    ; requiredProviderValidation =
        "replacement base unit"
        ∷ "DimensionCarrier and dimensionOfUnit"
        ∷ "conversionLaw"
        ∷ "Candidate256TSFVBindingLaw"
        ∷ "dimensionalPreservationLaw"
        ∷ []
    ; acceptedOnlyIfProviderBound =
        "A replacement base unit is admissible only if it supplies all W4 required provider fields"
        ∷ []
    ; rejectedInterpretations =
        "provider preference without typed fields"
        ∷ "unvalidated unit choice"
        ∷ []
    ; constructsPhysicalUnitAuthority =
        false
    ; constructsCandidate256PhysicalCalibrationAuthorityToken =
        false
    ; promotesW4 =
        false
    }

canonicalW4BaseUnitCandidateRoutes :
  List W4BaseUnitCandidateAuthorityRoute
canonicalW4BaseUnitCandidateRoutes =
  protonMassCODATACandidateRoute
  ∷ dyConventionNaturalUnitCandidateRoute
  ∷ providerSuppliedOtherBaseUnitCandidateRoute
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

    candidateBaseUnitRoutes :
      List W4BaseUnitCandidateAuthorityRoute

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

record W4QuotientSensitiveCrossBandWitnessSurface
  (law : Handoff.QuotientLawAtWitness
    Next.canonicalCandidate256QuotientLaw) :
  Setω where
  field
    status :
      W4QuotientSensitiveCrossBandWitnessStatus

    selectedRchemRelation :
      TSFV.Candidate256RchemRelationAtWitness law

    quotientInvolution :
      Surrogate.Candidate256QuotientClass →
      Surrogate.Candidate256QuotientClass

    quotientInvolutionIsT :
      quotientInvolution ≡ TSFV.candidate256QuotientT

    quotientInvolutionInvolutive :
      (q : Surrogate.Candidate256QuotientClass) →
      quotientInvolution (quotientInvolution q) ≡ q

    positiveWitnessClass :
      Surrogate.Candidate256QuotientClass

    negativeWitnessClass :
      Surrogate.Candidate256QuotientClass

    positiveWitnessClassIsCanonicalLeft :
      positiveWitnessClass ≡ Surrogate.candidate256LeftQuotientClass

    negativeWitnessClassIsCanonicalRight :
      negativeWitnessClass ≡ Surrogate.candidate256RightQuotientClass

    tsfvCompatibilityWitness :
      TSFV.Candidate256TritLchemDimensionalPreservation law

    positiveNonCollapseWitness :
      TSFV.candidate256TritQuotientCalibrationMap
        Surrogate.candidate256LeftQuotientClass
      ≡
      TSFV.candidate256TritQuotientCalibrationMap
        Surrogate.candidate256RightQuotientClass →
      ⊥

    tFlippedNonCollapseWitness :
      TSFV.candidate256TritQuotientCalibrationMap
        (TSFV.candidate256QuotientT Surrogate.candidate256LeftQuotientClass)
      ≡
      TSFV.candidate256TritQuotientCalibrationMap
        (TSFV.candidate256QuotientT Surrogate.candidate256RightQuotientClass) →
      ⊥

    providerReceiptBoundary :
      List String

    constructsProviderChemistryLawReceipt :
      Bool

    constructsCandidate256PhysicalCalibrationAuthorityToken :
      Bool

    constructsCandidate256PhysicalCalibrationExternalReceipt :
      Bool

    promotesW4 :
      Bool

record W4PhysicalUnitAuthorityProviderReceiptSurface : Setω where
  field
    status :
      W4PhysicalUnitAuthorityProviderReceiptSurfaceStatus

    request :
      W4PhysicalUnitAuthorityProviderRequest

    acceptedResponseMustBind :
      List String

    insufficientResponsePreserves :
      List String

    quotientSensitiveCrossBandWitness :
      (law : Handoff.QuotientLawAtWitness
        Next.canonicalCandidate256QuotientLaw) →
      W4QuotientSensitiveCrossBandWitnessSurface law

    receiptBoundary :
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
    ; candidateBaseUnitRoutes =
        canonicalW4BaseUnitCandidateRoutes
    ; acceptedResponseMustSupply =
        "a non-Nat physical unit carrier with an explicit baseUnit"
        ∷ "a dimension carrier and dimensionOfUnit map"
        ∷ "a conversion law to SI units or to an explicitly named natural-unit convention"
        ∷ "a dimensional preservation statement for the calibrated Candidate256/TSFV map"
        ∷ "a provider-bound base-unit citation/checksum/value packet; proton mass and DY natural units are only candidate routes until this is supplied"
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
        ∷ "proton mass or CODATA named without provider-bound value, uncertainty, unit convention, checksum/citation, and conversion law"
        ∷ "DY luminosity or pressure-decomposition diagnostics without AcceptedDYLuminosityConventionAuthorityReceipt"
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

canonicalW4QuotientSensitiveCrossBandWitnessSurface :
  (law : Handoff.QuotientLawAtWitness
    Next.canonicalCandidate256QuotientLaw) →
  W4QuotientSensitiveCrossBandWitnessSurface law
canonicalW4QuotientSensitiveCrossBandWitnessSurface law =
  record
    { status =
        quotientSensitiveWitnessAvailableAtInternalTSFVLevelOnly
    ; selectedRchemRelation =
        TSFV.candidate256RchemRelationAtWitness law
    ; quotientInvolution =
        TSFV.candidate256QuotientT
    ; quotientInvolutionIsT =
        refl
    ; quotientInvolutionInvolutive =
        TSFV.candidate256QuotientTInvolutive
    ; positiveWitnessClass =
        Surrogate.candidate256LeftQuotientClass
    ; negativeWitnessClass =
        Surrogate.candidate256RightQuotientClass
    ; positiveWitnessClassIsCanonicalLeft =
        refl
    ; negativeWitnessClassIsCanonicalRight =
        refl
    ; tsfvCompatibilityWitness =
        TSFV.candidate256TritLchemDimensionalPreservationAtWitness law
    ; positiveNonCollapseWitness =
        TSFV.candidate256TritNontrivialSeparation
    ; tFlippedNonCollapseWitness =
        TSFV.candidate256TritNontrivialSeparationAfterT
    ; providerReceiptBoundary =
        "This surface is parameterized by an existing QuotientLawAtWitness; it does not construct the cross-band law witness"
        ∷ "The quotient-sensitive content is internal TSFV structure: T involution, T-invariance, positive non-collapse, and T-flipped non-collapse"
        ∷ "A provider chemistry-law receipt must still bind this witness to external physical-unit authority before consumption"
        ∷ "No Candidate256PhysicalCalibrationAuthorityToken, external receipt, or W4 promotion is constructed"
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

canonicalW4PhysicalUnitAuthorityProviderReceiptSurface :
  W4PhysicalUnitAuthorityProviderReceiptSurface
canonicalW4PhysicalUnitAuthorityProviderReceiptSurface =
  record
    { status =
        providerReceiptSurfaceOnlyAwaitingExternalAuthority
    ; request =
        canonicalW4PhysicalUnitAuthorityProviderRequest
    ; acceptedResponseMustBind =
        "the exact request surface and provider payload version being answered"
        ∷ "external PhysicalUnitCarrier, baseUnit, DimensionCarrier, dimensionOfUnit, conversionTarget, and conversionLaw"
        ∷ "provider-bound base-unit citation/checksum/value/uncertainty packet"
        ∷ "Candidate256TSFVBindingLaw and calibratedScaleMapFactorsThroughNat if using the current receipt shape"
        ∷ "dimensionalPreservationLaw and dimensionalPreservationAtWitness over the Candidate256 quotient-law witness"
        ∷ "external Candidate256PhysicalCalibrationAuthorityToken artifact and Candidate256PhysicalCalibrationExternalReceipt payload"
        ∷ "provider chemistry-law receipt if the response consumes the quotient-sensitive cross-band witness"
        ∷ []
    ; insufficientResponsePreserves =
        "missing authority token keeps Candidate256PhysicalCalibrationAuthorityToken constructorless locally"
        ∷ "missing external unit carrier/baseUnit keeps the TSFV diagnostic carrier non-authoritative"
        ∷ "missing quotient-sensitive chemistry receipt keeps R-chem witness selection non-promoting"
        ∷ "missing dimensional preservation keeps W4 physical calibration blocked"
        ∷ []
    ; quotientSensitiveCrossBandWitness =
        canonicalW4QuotientSensitiveCrossBandWitnessSurface
    ; receiptBoundary =
        "This is a provider response/receipt surface, not the receipt itself"
        ∷ "Accepted responses must be external artifacts satisfying the named fields; local strings are not authority"
        ∷ "Insufficient or rejected responses preserve W4 as blocked and should identify missing typed fields"
        ∷ "This surface does not construct Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "This surface does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "This surface does not promote W4"
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
