module DASHI.Geometry.SpacetimeHistoryWorldTubeRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Geometry.SpacetimeHistoryWorldTube
open import DASHI.Empirical.GoogleTimelineSpacetimeBridge

------------------------------------------------------------------------
-- Compact import surface and canonical witnesses for the spacetime-history
-- tranche.  These witnesses prove the intended fail-closed flags reduce by
-- construction; they do not claim empirical completeness or metric accuracy.

canonicalPosition : SpatialSample
canonicalPosition =
  mkSpatialSample 10 20 3 "local projected coordinates"

canonicalObservation : TimelineObservation
canonicalObservation =
  mkUncertainTimelineObservation
    0
    100
    "home"
    canonicalPosition
    5
    stationaryMode
    "Google Timeline normalized export"

canonicalSection : WorldTubeSection
canonicalSection =
  mkWorldTubeSection canonicalObservation 5 12 1

canonicalHistory : SpacetimeHistory
canonicalHistory =
  mkSpacetimeHistory
    "subject-controlled personal archive"
    "local projected coordinates"
    (canonicalObservation ∷ [])
    (canonicalSection ∷ [])
    true
    refl
    false
    refl

canonicalPresentSlice : PresentSlice
canonicalPresentSlice =
  mkPresentSliceOf 100 (canonicalSection ∷ [])

canonicalImportReceipt : TimelineImportReceipt
canonicalImportReceipt =
  mkTimelineImportReceiptOf
    0
    100
    "home"
    "local projected coordinates"
    10
    20
    3
    5
    stationaryMode
    "Google Timeline normalized export"
    importedStatus
    true

canonicalSemanticContext : TimelineSemanticContext
canonicalSemanticContext =
  mkTimelineSemanticContext
    "embodied subject"
    "self and household"
    "personal archive"
    []
    "A situated mobility observation, not a complete experience"

canonicalIntegratedRow : IntegratedTimelineRow
canonicalIntegratedRow =
  integrateTimelineRow canonicalSemanticContext 12 1 canonicalImportReceipt

canonicalDataset : TimelineDatasetReceipt
canonicalDataset =
  mkTimelineDatasetReceiptOf
    "personal mobility history"
    (canonicalIntegratedRow ∷ [])

observationExactnessFailsClosed :
  observationIsExact canonicalObservation ≡ false
observationExactnessFailsClosed = refl

historyCandidateOnlyWitness :
  historyCandidateOnly canonicalHistory ≡ true
historyCandidateOnlyWitness = refl

historyCompletenessFailsClosed :
  historyCompleteLifeRecovery canonicalHistory ≡ false
historyCompletenessFailsClosed = refl

presentSliceIsNotWholeHistory :
  sliceIsWholeHistory canonicalPresentSlice ≡ false
presentSliceIsNotWholeHistory = refl

importExactnessFailsClosed :
  receiptExactPositionClaim canonicalImportReceipt ≡ false
importExactnessFailsClosed = refl

vendorInferenceSeparatedFromExperience :
  integratedVendorInferenceIsNotExperience canonicalIntegratedRow ≡ true
vendorInferenceSeparatedFromExperience = refl

datasetMissingnessAcknowledged :
  datasetMissingRowsAcknowledged canonicalDataset ≡ true
datasetMissingnessAcknowledged = refl

datasetCompletenessFailsClosed :
  datasetCompleteExperienceClaim canonicalDataset ≡ false
datasetCompletenessFailsClosed = refl

datasetAuthorityFailsClosed :
  datasetAuthorityClaim canonicalDataset ≡ false
datasetAuthorityFailsClosed = refl
