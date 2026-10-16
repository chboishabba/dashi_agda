module DASHI.Biology.KitzerowAttributionAcquisitionStatusExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.KitzerowAttributionEvidenceLineageExact as Lineage
import DASHI.Chemistry.LineageAttributionAcquisitionFrontierExact as Frontier

------------------------------------------------------------------------
-- DIRECTION-SENSITIVE ATTRIBUTION ACQUISITION STATUS
------------------------------------------------------------------------

data AttributionPaymentStatus : Set where
  originatorReportOnly : AttributionPaymentStatus
  publicLinkUninspected : AttributionPaymentStatus
  chronologyPartiallyPaid : AttributionPaymentStatus
  derivationTraceUnpaid : AttributionPaymentStatus
  directUsePaid : AttributionPaymentStatus

record AttributionAcquisitionStatus : Set where
  constructor attributionAcquisitionStatus
  field
    key : String
    status : AttributionPaymentStatus
    acquisitionReference : String
    paidCoordinate : String
    unpaidCoordinate : String
    temporalConstraint : String

open AttributionAcquisitionStatus public

stanfordDirectionalStatus : AttributionAcquisitionStatus
stanfordDirectionalStatus =
  attributionAcquisitionStatus
    "P1 Stanford"
    publicLinkUninspected
    "LineageAttributionAcquisitionFrontierExact.stanfordContactArtifact"
    "originator-reported 2023-11-27 contact plus discoverable link pointer"
    "inspect/authenticate message contents and metadata; if temporally prior to the comparison it may pay exposure, but direct use/derivation remains separately unpaid"
    "authenticated pre-publication exposure is relevant to access/opportunity but is not sufficient by itself for derivation"

brazilDirectionalStatus : AttributionAcquisitionStatus
brazilDirectionalStatus =
  attributionAcquisitionStatus
    "P2 Brazil/MDPI"
    originatorReportOnly
    "LineageAttributionAcquisitionFrontierExact.brazilCorrespondenceArtifact"
    "originator report of post-publication complaint/response chronology"
    "authenticate later correspondence for response history; separately acquire P4 pre-publication manuscript/exposure trace to test derivation"
    "post-publication contact cannot retroactively pay pre-publication exposure"

iaccDirectionalStatus : AttributionAcquisitionStatus
iaccDirectionalStatus =
  attributionAcquisitionStatus
    "P3 IACC/MedMaps"
    originatorReportOnly
    "LineageAttributionAcquisitionFrontierExact.iaccMedMapsContactArtifact"
    "originator-reported exposure-chain narrative"
    "underlying messages and institutional chronology; if authenticated, exposure remains distinct from direct use/derivation"
    "temporal order relative to the relevant IACC material must be established before the contact can pay an exposure coordinate"

comparisonDerivationTraceStatus : AttributionAcquisitionStatus
comparisonDerivationTraceStatus =
  attributionAcquisitionStatus
    "P4 comparison manuscript/exposure derivation trace"
    derivationTraceUnpaid
    "LineageAttributionAcquisitionFrontierExact.comparisonManuscriptHistoryArtifact"
    "no generic derivation upgrade paid"
    "versioned pre-publication manuscript/preprint/draft or authenticated earlier exposure trace tied to a specific later textual/idea/process/result manifestation"
    "direction must run from an identifiable upstream source/exposure state to the relevant later manifestation; later republication, citation count or post-publication contact cannot substitute"

canonicalKitzerowAttributionAcquisitionStatuses : List AttributionAcquisitionStatus
canonicalKitzerowAttributionAcquisitionStatuses =
  stanfordDirectionalStatus
  ∷ brazilDirectionalStatus
  ∷ iaccDirectionalStatus
  ∷ comparisonDerivationTraceStatus
  ∷ []

record KitzerowAttributionAcquisitionBoundary : Set where
  constructor kitzerowAttributionAcquisitionBoundary
  field
    authenticatedContactEqualsDocumentedUse : Bool
    authenticatedContactEqualsDocumentedUseIsFalse : authenticatedContactEqualsDocumentedUse ≡ false
    laterCorrespondenceCanEstablishEarlierExposure : Bool
    laterCorrespondenceCanEstablishEarlierExposureIsFalse : laterCorrespondenceCanEstablishEarlierExposure ≡ false
    multipleDownstreamReportsCreateIndependentRoots : Bool
    multipleDownstreamReportsCreateIndependentRootsIsFalse : multipleDownstreamReportsCreateIndependentRoots ≡ false
    exactVersionedTraceCanUpgradeDerivationCoordinate : Bool
    exactVersionedTraceCanUpgradeDerivationCoordinateIsTrue : exactVersionedTraceCanUpgradeDerivationCoordinate ≡ true
    derivationUpgradeAutomaticallyProvesPlagiarismOrLegalInfringement : Bool
    derivationUpgradeAutomaticallyProvesPlagiarismOrLegalInfringementIsFalse :
      derivationUpgradeAutomaticallyProvesPlagiarismOrLegalInfringement ≡ false

open KitzerowAttributionAcquisitionBoundary public

canonicalKitzerowAttributionAcquisitionBoundary : KitzerowAttributionAcquisitionBoundary
canonicalKitzerowAttributionAcquisitionBoundary =
  kitzerowAttributionAcquisitionBoundary
    false refl
    false refl
    false refl
    true refl
    false refl

lineageBoundaryConsumed : Lineage.KitzerowAttributionLineageBoundary
lineageBoundaryConsumed = Lineage.canonicalKitzerowAttributionLineageBoundary

frontierConsumed : Frontier.LineageAttributionAcquisitionFrontier
frontierConsumed = Frontier.canonicalLineageAttributionAcquisitionFrontier
