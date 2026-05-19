module DASHI.Physics.Closure.HEPDataObservableSelectionDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataEmpiricalSourceCandidateDiagnostic as Source
import DASHI.Physics.Closure.HEPDataMeasurementSurfaceProjectionRejection as Projection
import DASHI.Physics.Closure.HEPDataObservableSchema as Schema

------------------------------------------------------------------------
-- HEP-B observable/table-column selection diagnostic.
--
-- The schema module defines the shape of an eventual HEPDataObservable.
-- This module records the next selection gate only: a named physical
-- observable and a concrete record/table/column/row candidate must be selected
-- before any calibration or MeasurementSurface projection can be attempted.
-- No concrete in-repo candidate is promoted here because the available source
-- surfaces still lack an accepted authority receipt and local checksum binding.

record NamedPhysicalObservableSelection : Set where
  field
    observableName :
      String

    dashiObservableTarget :
      String

    comparisonLawTarget :
      String

    physicsMeaning :
      String

    unitExpectation :
      String

record HEPDataRecordTableColumnRowSelectionCandidate : Set where
  field
    recordSemantics :
      Schema.HEPDataRecordSemantics

    tableSemantics :
      Schema.HEPDataTableSemantics

    selectedObservableColumn :
      String

    selectedRowPredicate :
      String

    localChecksumOrHash :
      Schema.HEPDataLocalChecksumOrHash

    provenanceSemantics :
      Schema.HEPDataProvenanceSemantics

data SelectionRequirementBeforeCalibrationProjection : Set where
  requiresNamedPhysicalObservable :
    SelectionRequirementBeforeCalibrationProjection
  requiresRecordTableColumnRowSelectionCandidate :
    SelectionRequirementBeforeCalibrationProjection
  requiresLocalChecksumBinding :
    SelectionRequirementBeforeCalibrationProjection
  requiresAcceptedDatasetAuthority :
    SelectionRequirementBeforeCalibrationProjection
  requiresNoProjectionUntilSelectionClosed :
    SelectionRequirementBeforeCalibrationProjection

canonicalSelectionRequirementsBeforeCalibrationProjection :
  List SelectionRequirementBeforeCalibrationProjection
canonicalSelectionRequirementsBeforeCalibrationProjection =
  requiresNamedPhysicalObservable
  ∷ requiresRecordTableColumnRowSelectionCandidate
  ∷ requiresLocalChecksumBinding
  ∷ requiresAcceptedDatasetAuthority
  ∷ requiresNoProjectionUntilSelectionClosed
  ∷ []

data CurrentHEPDataObservableSelectionStatus : Set where
  selectionBlockedAwaitingConcreteAuthorizedChecksumCandidate :
    CurrentHEPDataObservableSelectionStatus

data HEPDataObservableSelectionMissingSurface : Set where
  missingNamedPhysicalObservable :
    HEPDataObservableSelectionMissingSurface
  missingRecordIdentifier :
    HEPDataObservableSelectionMissingSurface
  missingTableIdentifier :
    HEPDataObservableSelectionMissingSurface
  missingObservableColumnIdentifier :
    HEPDataObservableSelectionMissingSurface
  missingRowSelectionPredicate :
    HEPDataObservableSelectionMissingSurface
  missingLocalChecksumOrHash :
    HEPDataObservableSelectionMissingSurface
  missingAcceptedAuthorityForSelection :
    HEPDataObservableSelectionMissingSurface

canonicalHEPDataObservableSelectionMissingSurfaces :
  List HEPDataObservableSelectionMissingSurface
canonicalHEPDataObservableSelectionMissingSurfaces =
  missingNamedPhysicalObservable
  ∷ missingRecordIdentifier
  ∷ missingTableIdentifier
  ∷ missingObservableColumnIdentifier
  ∷ missingRowSelectionPredicate
  ∷ missingLocalChecksumOrHash
  ∷ missingAcceptedAuthorityForSelection
  ∷ []

data HEPDataObservableSelectionReceipt : Set where

selectionReceiptImpossibleHere :
  HEPDataObservableSelectionReceipt →
  ⊥
selectionReceiptImpossibleHere ()

record HEPDataObservableSelectionDiagnostic : Setω where
  field
    sourceCandidateDiagnostic :
      Source.HEPDataEmpiricalSourceCandidateDiagnostic

    projectionRejection :
      Projection.HEPDataMeasurementSurfaceProjectionRejection

    sourceCandidatesStillNonPromoting :
      Source.HEPDataEmpiricalSourceCandidateDiagnostic.candidateStatus
        sourceCandidateDiagnostic
      ≡
      Source.sourceCandidatesPresentButNonPromoting

    projectionStillRejected :
      Projection.HEPDataMeasurementSurfaceProjectionRejection.currentStatus
        projectionRejection
      ≡
      Projection.rejectedMissingProjectionContract

    selectionStatus :
      CurrentHEPDataObservableSelectionStatus

    namedPhysicalObservableSelected :
      Bool

    recordTableColumnRowCandidateSelected :
      Bool

    localChecksumBound :
      Bool

    acceptedAuthorityAvailable :
      Bool

    requirementsBeforeCalibrationProjection :
      List SelectionRequirementBeforeCalibrationProjection

    requirementsAreCanonical :
      requirementsBeforeCalibrationProjection
      ≡
      canonicalSelectionRequirementsBeforeCalibrationProjection

    missingSelectionSurfaces :
      List HEPDataObservableSelectionMissingSurface

    missingSelectionSurfacesAreCanonical :
      missingSelectionSurfaces
      ≡
      canonicalHEPDataObservableSelectionMissingSurfaces

    schemaFieldsThisSelectionMustEventuallyPopulate :
      List Schema.HEPDataObservableRequiredField

    noConcreteSelectionReason :
      String

    requiredSelectionShape :
      List String

    downstreamBlockedUntilSelection :
      List String

    nonPromotionBoundary :
      List String

    coordinationMapNodeText :
      String

    coordinationMapEdgeText :
      String

    noSelectionReceiptHere :
      HEPDataObservableSelectionReceipt →
      ⊥

canonicalHEPDataObservableSelectionDiagnostic :
  HEPDataObservableSelectionDiagnostic
canonicalHEPDataObservableSelectionDiagnostic =
  record
    { sourceCandidateDiagnostic =
        Source.canonicalHEPDataEmpiricalSourceCandidateDiagnostic
    ; projectionRejection =
        Projection.canonicalHEPDataMeasurementSurfaceProjectionRejection
    ; sourceCandidatesStillNonPromoting =
        refl
    ; projectionStillRejected =
        refl
    ; selectionStatus =
        selectionBlockedAwaitingConcreteAuthorizedChecksumCandidate
    ; namedPhysicalObservableSelected =
        false
    ; recordTableColumnRowCandidateSelected =
        false
    ; localChecksumBound =
        false
    ; acceptedAuthorityAvailable =
        false
    ; requirementsBeforeCalibrationProjection =
        canonicalSelectionRequirementsBeforeCalibrationProjection
    ; requirementsAreCanonical =
        refl
    ; missingSelectionSurfaces =
        canonicalHEPDataObservableSelectionMissingSurfaces
    ; missingSelectionSurfacesAreCanonical =
        refl
    ; schemaFieldsThisSelectionMustEventuallyPopulate =
        Schema.requiredRecordSemantics
        ∷ Schema.requiredTableSemantics
        ∷ Schema.requiredLocalChecksumOrHash
        ∷ Schema.requiredProvenanceSemantics
        ∷ []
    ; noConcreteSelectionReason =
        "local HEPData source candidates exist, but no single named physical observable plus record/table/column/row candidate is authority-accepted and checksum-bound in this repo"
    ; requiredSelectionShape =
        "one named physical observable with Dashi observable target and comparison-law target"
        ∷ "one HEPData record identifier/version/submission/DOI/source landing page"
        ∷ "one HEPData table name/path/version"
        ∷ "one selected observable column and one row-selection predicate"
        ∷ "one local checksum/hash binding for the selected artifact"
        ∷ "one provenance surface for retrieval, adapter, transform log, and use terms"
        ∷ []
    ; downstreamBlockedUntilSelection =
        "HEP-C unit/dimension calibration must not bind to an unnamed or unselected observable"
        ∷ "HEP-D MeasurementSurface projection remains rejected until selection, metric law, and authority close"
        ∷ "W3 accepted-authority and W8 origin-promotion routes remain unavailable from this diagnostic"
        ∷ []
    ; nonPromotionBoundary =
        "This module constructs no HEPDataObservable value"
        ∷ "This module selects no concrete HEPData record, table, row, or column"
        ∷ "This module fabricates no checksum, no authority token, no calibration map, and no projection"
        ∷ "This module promotes no W3 accepted-authority receipt and no W8 origin-promotion receipt"
        ∷ []
    ; coordinationMapNodeText =
        "rectangle \"HEP-B\\nobservable/table-column selection\\ntyped diagnostic\\nno fake selection\" as HEPDATA_HEPB #fef3c7"
    ; coordinationMapEdgeText =
        "HEPDATA_QUEUE --> HEPDATA_HEPB : HEP-B observable/table-column selection diagnostic\nHEPDATA_HEPB --> Plateau : calibration/projection blocked until checksum-bound selection + authority\nHEPDATA_HEPB --> HEPDATA_HEPD : projection remains rejected without selected candidate\nHEPDATA_HEPB --> W3 : no accepted-authority promotion"
    ; noSelectionReceiptHere =
        selectionReceiptImpossibleHere
    }
