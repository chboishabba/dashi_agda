module DASHI.Culture.AmyEskridgeViewpointSourceAttributionMigrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.ViewpointProvenanceBidiExact as V
import DASHI.Culture.AmyEskridgeGravityMechanismCrossPollinationExact as Amy
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- AMY VIEWPOINT SOURCE ATTRIBUTION MIGRATION
--
-- Legacy ViewpointReceipt.sourceReference is useful provenance text but is not
-- silently treated as a fully migrated attributed source.  Located access
-- routes, unresolved metadata, and original-custody questions stay separate.
------------------------------------------------------------------------

data CarrierLocationStatus : Set where
  locatedCarrierURL : String → CarrierLocationStatus
  carrierLocationUnresolved : CarrierLocationStatus

data CanonicalTitleStatus : Set where
  canonicalTitleKnown : String → CanonicalTitleStatus
  canonicalTitleUnresolved : CanonicalTitleStatus

data InspectionStatus : Set where
  inspectedOn : String → InspectionStatus
  inspectionDateNotPinned : InspectionStatus

data OriginalCustodyStatus : Set where
  originalCustodyResolved : String → OriginalCustodyStatus
  originalCustodyUnresolved : OriginalCustodyStatus

record AmyHistoricalSourceCandidate : Set where
  constructor amy-historical-source-candidate
  field
    carrierDescription : String
    responsibleBodyOrSpeaker : String
    titleStatus : CanonicalTitleStatus
    carrierLocation : CarrierLocationStatus
    inspectionStatus : InspectionStatus
    originalCustodyStatus : OriginalCustodyStatus
    exactBoundedUse : String

open AmyHistoricalSourceCandidate public

------------------------------------------------------------------------
-- Located in-repo acquisition route.  The repository's 2026-09-05 acquisition
-- notes pin this URL, but do not supply enough here to invent a canonical page
-- title or an original-recording custody chain.
------------------------------------------------------------------------

blockedEpistemologyZoomCandidate : AmyHistoricalSourceCandidate
blockedEpistemologyZoomCandidate =
  amy-historical-source-candidate
    "Blocked Epistemology archive of Amy Eskridge Zoom material"
    "Amy Eskridge / Blocked Epistemology archive"
    canonicalTitleUnresolved
    (locatedCarrierURL
      "https://blockedepistemology.substack.com/p/archive-amy-eskridge-zoom")
    (inspectedOn "2026-09-05")
    originalCustodyUnresolved
    "historical first-person viewpoint evidence concerning public disclosure, anti-gravity belief, suppression claims, and secrecy critique; not physical validation"

------------------------------------------------------------------------
-- HAL5 material is repeatedly cited by the existing Amy lane, but a canonical
-- stable carrier and exact title/segment are not pinned in this branch.  Keep
-- those as residuals instead of manufacturing bibliographic metadata.
------------------------------------------------------------------------

hal5December2018Candidate : AmyHistoricalSourceCandidate
hal5December2018Candidate =
  amy-historical-source-candidate
    "HAL5 December 2018 Amy Eskridge presentation"
    "Amy Eskridge / HAL5"
    canonicalTitleUnresolved
    carrierLocationUnresolved
    inspectionDateNotPinned
    originalCustodyUnresolved
    "historical presentation context for the Institute, team, anti-gravity research programme, and public scientific/disclosure posture"

------------------------------------------------------------------------
-- Exact migration residuals.
------------------------------------------------------------------------

data AmyViewpointAttributionResidual : Set where
  missingZoomCanonicalTitle : AmyViewpointAttributionResidual
  missingZoomOriginalRecordingCustody : AmyViewpointAttributionResidual
  missingZoomExactSegmentLocator : AmyViewpointAttributionResidual
  missingHAL5CanonicalTitle : AmyViewpointAttributionResidual
  missingHAL5StableCarrier : AmyViewpointAttributionResidual
  missingHAL5InspectionDate : AmyViewpointAttributionResidual
  missingHAL5ExactSegmentLocator : AmyViewpointAttributionResidual

currentAmyViewpointAttributionResiduals : List AmyViewpointAttributionResidual
currentAmyViewpointAttributionResiduals =
  missingZoomCanonicalTitle ∷
  missingZoomOriginalRecordingCustody ∷
  missingZoomExactSegmentLocator ∷
  missingHAL5CanonicalTitle ∷
  missingHAL5StableCarrier ∷
  missingHAL5InspectionDate ∷
  missingHAL5ExactSegmentLocator ∷ []

producerForAmyViewpointAttributionResidual :
  AmyViewpointAttributionResidual → Search.ProducerClass
producerForAmyViewpointAttributionResidual missingZoomCanonicalTitle =
  Search.attributionProducer
producerForAmyViewpointAttributionResidual missingZoomOriginalRecordingCustody =
  Search.identityProducer
producerForAmyViewpointAttributionResidual missingZoomExactSegmentLocator =
  Search.discriminatorProducer
producerForAmyViewpointAttributionResidual missingHAL5CanonicalTitle =
  Search.attributionProducer
producerForAmyViewpointAttributionResidual missingHAL5StableCarrier =
  Search.propositionSourceProducer
producerForAmyViewpointAttributionResidual missingHAL5InspectionDate =
  Search.temporalProducer
producerForAmyViewpointAttributionResidual missingHAL5ExactSegmentLocator =
  Search.discriminatorProducer

------------------------------------------------------------------------
-- Bind migration to the exact existing viewpoint receipt rather than creating
-- a replacement Amy belief object.
------------------------------------------------------------------------

record AmyViewpointAttributionMigration : Set where
  constructor amy-viewpoint-attribution-migration
  field
    viewpointReceipt : V.ViewpointReceipt
    viewpointReceiptIsCanonical : viewpointReceipt ≡ Amy.amyExoticPropulsionReceipt
    legacySourceReference : String
    legacySourceReferenceMatches :
      V.sourceReference viewpointReceipt ≡ legacySourceReference
    zoomCandidate : AmyHistoricalSourceCandidate
    hal5Candidate : AmyHistoricalSourceCandidate
    residuals : List AmyViewpointAttributionResidual

open AmyViewpointAttributionMigration public

canonicalAmyViewpointAttributionMigration : AmyViewpointAttributionMigration
canonicalAmyViewpointAttributionMigration =
  amy-viewpoint-attribution-migration
    Amy.amyExoticPropulsionReceipt
    refl
    (V.sourceReference Amy.amyExoticPropulsionReceipt)
    refl
    blockedEpistemologyZoomCandidate
    hal5December2018Candidate
    currentAmyViewpointAttributionResiduals

record AmyViewpointAttributionMigrationBoundary : Set where
  constructor amy-viewpoint-attribution-migration-boundary
  field
    legacySourceStringEqualsFullyAttributedCarrier : Bool
    locatedArchiveEqualsOriginalRecordingCustody : Bool
    missingHAL5CarrierMayBeGuessed : Bool
    incompleteMigrationInvalidatesAllHistoricalContext : Bool
    migrationResidualMayScheduleProducer : Bool
    migratedHistoricalSourceAutomaticallyPaysPhysicalClaim : Bool

canonicalAmyViewpointAttributionMigrationBoundary :
  AmyViewpointAttributionMigrationBoundary
canonicalAmyViewpointAttributionMigrationBoundary =
  amy-viewpoint-attribution-migration-boundary
    false false false false true false
