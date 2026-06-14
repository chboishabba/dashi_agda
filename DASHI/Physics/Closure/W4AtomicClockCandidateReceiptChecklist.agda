module DASHI.Physics.Closure.W4AtomicClockCandidateReceiptChecklist where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AtomicClockCandidate256DimensionAdapter as Dimension
import DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest as Adapter
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as External
import DASHI.Promotion.SIDefiningConstantsAuthorityArtifactRequest as SI

------------------------------------------------------------------------
-- W4/Candidate256 atomic-clock receipt checklist.
--
-- This is the atomic-clock-specific checklist surface for the external
-- Candidate256PhysicalCalibrationExternalReceipt.  It aligns every receipt
-- field with the current checked source/ref, but keeps every row open and
-- fail-closed.  It is not an authority artifact and does not construct the
-- external receipt.

data AtomicClockCandidateReceiptField : Set where
  calibrationAuthorityField :
    AtomicClockCandidateReceiptField
  physicalUnitCarrierField :
    AtomicClockCandidateReceiptField
  physicalDimensionVectorField :
    AtomicClockCandidateReceiptField
  natToUnitCalibrationMapField :
    AtomicClockCandidateReceiptField
  calibratedQuotientScaleMapField :
    AtomicClockCandidateReceiptField
  calibratedScaleMapFactorsThroughNatField :
    AtomicClockCandidateReceiptField
  dimensionalPreservationLawField :
    AtomicClockCandidateReceiptField
  dimensionalPreservationAtWitnessField :
    AtomicClockCandidateReceiptField
  physicalUnitCarrierLabelField :
    AtomicClockCandidateReceiptField
  physicalDimensionVectorLabelField :
    AtomicClockCandidateReceiptField
  natToUnitCalibrationMapLabelField :
    AtomicClockCandidateReceiptField
  calibratedQuotientScaleMapLabelField :
    AtomicClockCandidateReceiptField
  factorizationLabelField :
    AtomicClockCandidateReceiptField
  dimensionalPreservationLabelField :
    AtomicClockCandidateReceiptField

data AtomicClockCandidateChecklistRowStatus : Set where
  openExternalReceiptField :
    AtomicClockCandidateChecklistRowStatus

record AtomicClockCandidateReceiptChecklistRow : Set where
  field
    fieldKey :
      AtomicClockCandidateReceiptField

    receiptFieldName :
      String

    currentSourceModule :
      String

    currentSourceRef :
      String

    rowStatus :
      AtomicClockCandidateChecklistRowStatus

    rowSatisfied :
      Bool

    rowSatisfiedIsFalse :
      rowSatisfied ≡ false

    dependencyLabel :
      String

    guardLabel :
      String

open AtomicClockCandidateReceiptChecklistRow public

mkOpenRow :
  AtomicClockCandidateReceiptField →
  String →
  String →
  String →
  String →
  AtomicClockCandidateReceiptChecklistRow
mkOpenRow key fieldName sourceModule sourceRef dependency =
  record
    { fieldKey =
        key
    ; receiptFieldName =
        fieldName
    ; currentSourceModule =
        sourceModule
    ; currentSourceRef =
        sourceRef
    ; rowStatus =
        openExternalReceiptField
    ; rowSatisfied =
        false
    ; rowSatisfiedIsFalse =
        refl
    ; dependencyLabel =
        dependency
    ; guardLabel =
        "terminal guard: Candidate256PhysicalCalibrationExternalReceipt remains impossible without an external Candidate256PhysicalCalibrationAuthorityToken"
    }

calibrationAuthorityChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
calibrationAuthorityChecklistRow =
  mkOpenRow
    calibrationAuthorityField
    "calibrationAuthority"
    "DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation"
    "canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus.requiredAuthorityArtifact"
    "external Candidate256PhysicalCalibrationAuthorityToken artifact; SI manifest rows are only authority-artifact requests"

physicalUnitCarrierChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
physicalUnitCarrierChecklistRow =
  mkOpenRow
    physicalUnitCarrierField
    "physicalUnitCarrier"
    "DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest"
    "canonicalAtomicClockW4ReceiptAdapterRequest.physicalUnitCarrier"
    "atomic-clock SI time/frequency carrier from AtomicClockSISecondCalibrationBridge"

physicalDimensionVectorChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
physicalDimensionVectorChecklistRow =
  mkOpenRow
    physicalDimensionVectorField
    "physicalDimensionVector"
    "DASHI.Physics.Closure.AtomicClockCandidate256DimensionAdapter"
    "canonicalAtomicClockCandidate256DimensionAdapter.candidate256SecondDimension"
    "Candidate256 dimension vector for SI second; source checked by the dimension adapter"

natToUnitCalibrationMapChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
natToUnitCalibrationMapChecklistRow =
  mkOpenRow
    natToUnitCalibrationMapField
    "natToUnitCalibrationMap"
    "DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest"
    "canonicalAtomicClockW4ReceiptAdapterRequest.natToUnitCalibrationMap"
    "Nat-to-SI-second calibration route from the atomic-clock adapter"

calibratedQuotientScaleMapChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
calibratedQuotientScaleMapChecklistRow =
  mkOpenRow
    calibratedQuotientScaleMapField
    "calibratedQuotientScaleMap"
    "DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest"
    "canonicalAtomicClockW4ReceiptAdapterRequest.calibratedQuotientScaleMap"
    "Candidate256 quotient-class to SI-second route from the atomic-clock adapter"

calibratedScaleMapFactorsThroughNatChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
calibratedScaleMapFactorsThroughNatChecklistRow =
  mkOpenRow
    calibratedScaleMapFactorsThroughNatField
    "calibratedScaleMapFactorsThroughNat"
    "DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest"
    "canonicalAtomicClockAdapterFactorizationMatchesBridge"
    "factorization through candidate256SurrogateScale; checked but still not authority-bearing"

dimensionalPreservationLawChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
dimensionalPreservationLawChecklistRow =
  mkOpenRow
    dimensionalPreservationLawField
    "dimensionalPreservationLaw"
    "DASHI.Physics.Closure.AtomicClockCandidate256DimensionAdapter"
    "AtomicClockCandidate256DimensionalPreservationRequest"
    "law family for preserving SI-second dimension at Candidate256 quotient-law witnesses"

dimensionalPreservationAtWitnessChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
dimensionalPreservationAtWitnessChecklistRow =
  mkOpenRow
    dimensionalPreservationAtWitnessField
    "dimensionalPreservationAtWitness"
    "DASHI.Physics.Closure.AtomicClockCandidate256DimensionAdapter"
    "atomicClockCandidate256DimensionalPreservationRequested"
    "checked witness inhabitant for the atomic-clock dimension request; still not an external receipt"

physicalUnitCarrierLabelChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
physicalUnitCarrierLabelChecklistRow =
  mkOpenRow
    physicalUnitCarrierLabelField
    "physicalUnitCarrierLabel"
    "DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest"
    "canonicalAtomicClockW4ReceiptAdapterRequest.physicalUnitCarrierLabel"
    "label dependency for the SI time/frequency carrier"

physicalDimensionVectorLabelChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
physicalDimensionVectorLabelChecklistRow =
  mkOpenRow
    physicalDimensionVectorLabelField
    "physicalDimensionVectorLabel"
    "DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest"
    "canonicalAtomicClockW4ReceiptAdapterRequest.physicalDimensionVectorLabel"
    "label dependency for the SI second Candidate256 dimension vector"

natToUnitCalibrationMapLabelChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
natToUnitCalibrationMapLabelChecklistRow =
  mkOpenRow
    natToUnitCalibrationMapLabelField
    "natToUnitCalibrationMapLabel"
    "DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest"
    "canonicalAtomicClockW4ReceiptAdapterRequest.natToUnitCalibrationMapLabel"
    "label dependency for the Nat-to-unit calibration map"

calibratedQuotientScaleMapLabelChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
calibratedQuotientScaleMapLabelChecklistRow =
  mkOpenRow
    calibratedQuotientScaleMapLabelField
    "calibratedQuotientScaleMapLabel"
    "DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest"
    "canonicalAtomicClockW4ReceiptAdapterRequest.calibratedQuotientScaleMapLabel"
    "label dependency for the calibrated Candidate256 quotient scale map"

factorizationLabelChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
factorizationLabelChecklistRow =
  mkOpenRow
    factorizationLabelField
    "factorizationLabel"
    "DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest"
    "canonicalAtomicClockW4ReceiptAdapterRequest.factorizationLabel"
    "label dependency for the factorization law"

dimensionalPreservationLabelChecklistRow :
  AtomicClockCandidateReceiptChecklistRow
dimensionalPreservationLabelChecklistRow =
  mkOpenRow
    dimensionalPreservationLabelField
    "dimensionalPreservationLabel"
    "DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest"
    "canonicalAtomicClockW4ReceiptAdapterRequest.dimensionalPreservationLabel"
    "label dependency for dimensional preservation"

canonicalAtomicClockCandidateReceiptChecklistRows :
  List AtomicClockCandidateReceiptChecklistRow
canonicalAtomicClockCandidateReceiptChecklistRows =
  calibrationAuthorityChecklistRow
  ∷ physicalUnitCarrierChecklistRow
  ∷ physicalDimensionVectorChecklistRow
  ∷ natToUnitCalibrationMapChecklistRow
  ∷ calibratedQuotientScaleMapChecklistRow
  ∷ calibratedScaleMapFactorsThroughNatChecklistRow
  ∷ dimensionalPreservationLawChecklistRow
  ∷ dimensionalPreservationAtWitnessChecklistRow
  ∷ physicalUnitCarrierLabelChecklistRow
  ∷ physicalDimensionVectorLabelChecklistRow
  ∷ natToUnitCalibrationMapLabelChecklistRow
  ∷ calibratedQuotientScaleMapLabelChecklistRow
  ∷ factorizationLabelChecklistRow
  ∷ dimensionalPreservationLabelChecklistRow
  ∷ []

record AtomicClockCandidateReceiptNoPromotionSummary : Setω where
  field
    adapterRequest :
      Adapter.AtomicClockW4ReceiptAdapterRequest

    dimensionAdapter :
      Dimension.AtomicClockCandidate256DimensionAdapter

    siAuthorityArtifactManifest :
      SI.SIDefiningConstantsAuthorityArtifactRequestManifest

    externalCurrentStatus :
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    authorityTokenConstructed :
      Bool

    authorityTokenConstructedIsFalse :
      authorityTokenConstructed ≡ false

    externalReceiptConstructed :
      Bool

    externalReceiptConstructedIsFalse :
      externalReceiptConstructed ≡ false

    w4PhysicalCalibrationPromoted :
      Bool

    w4PhysicalCalibrationPromotedIsFalse :
      w4PhysicalCalibrationPromoted ≡ false

    siAuthorityArtifactLoaded :
      Bool

    siAuthorityArtifactLoadedIsFalse :
      siAuthorityArtifactLoaded ≡ false

    siAuthorityRowsPromoted :
      Bool

    siAuthorityRowsPromotedIsFalse :
      siAuthorityRowsPromoted ≡ false

    terminalReceiptGuard :
      External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

    noPromotionBoundary :
      List String

open AtomicClockCandidateReceiptNoPromotionSummary public

canonicalAtomicClockCandidateReceiptNoPromotionSummary :
  AtomicClockCandidateReceiptNoPromotionSummary
canonicalAtomicClockCandidateReceiptNoPromotionSummary =
  record
    { adapterRequest =
        Adapter.canonicalAtomicClockW4ReceiptAdapterRequest
    ; dimensionAdapter =
        Dimension.canonicalAtomicClockCandidate256DimensionAdapter
    ; siAuthorityArtifactManifest =
        SI.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; externalCurrentStatus =
        External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; authorityTokenConstructed =
        false
    ; authorityTokenConstructedIsFalse =
        refl
    ; externalReceiptConstructed =
        false
    ; externalReceiptConstructedIsFalse =
        refl
    ; w4PhysicalCalibrationPromoted =
        false
    ; w4PhysicalCalibrationPromotedIsFalse =
        refl
    ; siAuthorityArtifactLoaded =
        SI.SIDefiningConstantsAuthorityArtifactRequestManifest.artifactLoaded
          SI.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; siAuthorityArtifactLoadedIsFalse =
        refl
    ; siAuthorityRowsPromoted =
        SI.SIDefiningConstantsAuthorityArtifactRequestManifest.anyRowPromoted
          SI.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; siAuthorityRowsPromotedIsFalse =
        refl
    ; terminalReceiptGuard =
        External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    ; noPromotionBoundary =
        "Checklist only: every Candidate256PhysicalCalibrationExternalReceipt field is aligned to its current atomic-clock source/ref"
        ∷ "Every checklist row remains status=openExternalReceiptField and rowSatisfied=false"
        ∷ "The SI defining-constants manifest is only an authority-artifact request; artifactLoaded=false and anyRowPromoted=false"
        ∷ "No Candidate256PhysicalCalibrationAuthorityToken is constructed"
        ∷ "No Candidate256PhysicalCalibrationExternalReceipt is constructed"
        ∷ "No W4 physical-calibration promotion is constructed"
        ∷ External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.noPromotionBoundary
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    }

record AtomicClockCandidateReceiptChecklist : Setω where
  field
    adapterRequest :
      Adapter.AtomicClockW4ReceiptAdapterRequest

    dimensionAdapter :
      Dimension.AtomicClockCandidate256DimensionAdapter

    siAuthorityArtifactManifest :
      SI.SIDefiningConstantsAuthorityArtifactRequestManifest

    externalCurrentStatus :
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    requiredExternalReceiptFields :
      List AtomicClockCandidateReceiptField

    requiredExternalReceiptFieldCount :
      Nat

    checklistRows :
      List AtomicClockCandidateReceiptChecklistRow

    allRowsOpen :
      Bool

    allRowsOpenIsFalse :
      allRowsOpen ≡ false

    externalAuthorityConstructed :
      Bool

    externalAuthorityConstructedIsFalse :
      externalAuthorityConstructed ≡ false

    externalReceiptConstructed :
      Bool

    externalReceiptConstructedIsFalse :
      externalReceiptConstructed ≡ false

    w4PhysicalCalibrationPromoted :
      Bool

    w4PhysicalCalibrationPromotedIsFalse :
      w4PhysicalCalibrationPromoted ≡ false

    noPromotionSummary :
      AtomicClockCandidateReceiptNoPromotionSummary

    terminalGuard :
      External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

    checklistBoundary :
      List String

open AtomicClockCandidateReceiptChecklist public

canonicalAtomicClockCandidateRequiredReceiptFields :
  List AtomicClockCandidateReceiptField
canonicalAtomicClockCandidateRequiredReceiptFields =
  calibrationAuthorityField
  ∷ physicalUnitCarrierField
  ∷ physicalDimensionVectorField
  ∷ natToUnitCalibrationMapField
  ∷ calibratedQuotientScaleMapField
  ∷ calibratedScaleMapFactorsThroughNatField
  ∷ dimensionalPreservationLawField
  ∷ dimensionalPreservationAtWitnessField
  ∷ physicalUnitCarrierLabelField
  ∷ physicalDimensionVectorLabelField
  ∷ natToUnitCalibrationMapLabelField
  ∷ calibratedQuotientScaleMapLabelField
  ∷ factorizationLabelField
  ∷ dimensionalPreservationLabelField
  ∷ []

canonicalAtomicClockCandidateReceiptChecklist :
  AtomicClockCandidateReceiptChecklist
canonicalAtomicClockCandidateReceiptChecklist =
  record
    { adapterRequest =
        Adapter.canonicalAtomicClockW4ReceiptAdapterRequest
    ; dimensionAdapter =
        Dimension.canonicalAtomicClockCandidate256DimensionAdapter
    ; siAuthorityArtifactManifest =
        SI.canonicalSIDefiningConstantsAuthorityArtifactRequestManifest
    ; externalCurrentStatus =
        External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; requiredExternalReceiptFields =
        canonicalAtomicClockCandidateRequiredReceiptFields
    ; requiredExternalReceiptFieldCount =
        14
    ; checklistRows =
        canonicalAtomicClockCandidateReceiptChecklistRows
    ; allRowsOpen =
        false
    ; allRowsOpenIsFalse =
        refl
    ; externalAuthorityConstructed =
        false
    ; externalAuthorityConstructedIsFalse =
        refl
    ; externalReceiptConstructed =
        false
    ; externalReceiptConstructedIsFalse =
        refl
    ; w4PhysicalCalibrationPromoted =
        false
    ; w4PhysicalCalibrationPromotedIsFalse =
        refl
    ; noPromotionSummary =
        canonicalAtomicClockCandidateReceiptNoPromotionSummary
    ; terminalGuard =
        External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    ; checklistBoundary =
        "The checklist covers the authority token, carrier, dimension vector, maps, laws, witnesses, and labels required by Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "Current source refs come from AtomicClockW4ReceiptAdapterRequest, AtomicClockCandidate256DimensionAdapter, W4PhysicalCalibrationExternalReceiptObligation, and the SI authority-artifact request manifest"
        ∷ "Checked adapter values are not external authority: all rows remain open and rowSatisfied=false"
        ∷ "The terminal guard is the existing impossible receipt eliminator"
        ∷ "Authority-token construction, external receipt construction, and W4 physical-calibration promotion remain false"
        ∷ []
    }

canonicalAtomicClockCandidateChecklistFieldCountIs14 :
  AtomicClockCandidateReceiptChecklist.requiredExternalReceiptFieldCount
    canonicalAtomicClockCandidateReceiptChecklist
  ≡ 14
canonicalAtomicClockCandidateChecklistFieldCountIs14 =
  refl

canonicalAtomicClockCandidateChecklistRowsCanonical :
  AtomicClockCandidateReceiptChecklist.checklistRows
    canonicalAtomicClockCandidateReceiptChecklist
  ≡
  canonicalAtomicClockCandidateReceiptChecklistRows
canonicalAtomicClockCandidateChecklistRowsCanonical =
  refl

canonicalAtomicClockCandidateChecklistNoAuthority :
  AtomicClockCandidateReceiptChecklist.externalAuthorityConstructed
    canonicalAtomicClockCandidateReceiptChecklist
  ≡ false
canonicalAtomicClockCandidateChecklistNoAuthority =
  refl

canonicalAtomicClockCandidateChecklistNoReceipt :
  AtomicClockCandidateReceiptChecklist.externalReceiptConstructed
    canonicalAtomicClockCandidateReceiptChecklist
  ≡ false
canonicalAtomicClockCandidateChecklistNoReceipt =
  refl

canonicalAtomicClockCandidateChecklistNoPromotion :
  AtomicClockCandidateReceiptChecklist.w4PhysicalCalibrationPromoted
    canonicalAtomicClockCandidateReceiptChecklist
  ≡ false
canonicalAtomicClockCandidateChecklistNoPromotion =
  refl

canonicalAtomicClockCandidateChecklistTerminalGuard :
  External.Candidate256PhysicalCalibrationExternalReceipt →
  ⊥
canonicalAtomicClockCandidateChecklistTerminalGuard =
  AtomicClockCandidateReceiptChecklist.terminalGuard
    canonicalAtomicClockCandidateReceiptChecklist
