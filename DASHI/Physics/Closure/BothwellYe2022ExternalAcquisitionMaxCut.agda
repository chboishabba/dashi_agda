module DASHI.Physics.Closure.BothwellYe2022ExternalAcquisitionMaxCut where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BothwellYe2022PublicArtifactLocatorExact as Locator
import DASHI.Physics.Closure.BothwellYe2022GeodeticCalibrationExact as Geodetic
import DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftReceiptRequest as Request

------------------------------------------------------------------------
-- EXTERNAL ACQUISITION MAX-CUT FOR BOTHWELL/YE 2022
--
-- The public-source lane is already substantially paid.  Nature identifies
-- Tobias Bothwell and Jun Ye as corresponding authors and states that both
-- experimental data and analysis code are available from the corresponding
-- authors upon reasonable request.
--
-- This owner converts the remaining wall into a typed acquisition contract.
-- It deliberately separates:
--
--   A. bytes / numerical evidence that must come from the authors;
--   B. checksums, replay and consumer-ingestion work DASHI must perform after
--      those bytes arrive;
--   C. coordinates already paid publicly and therefore not re-requested.
--
-- Constructing the request packet is NOT evidence receipt, sending the request,
-- author response, raw-data acquisition, code acquisition, replay, acceptance,
-- or empirical promotion.
------------------------------------------------------------------------

record CorrespondingAuthorEndpoint : Set where
  field
    authorName : String
    email : String
    sourceRole : String

open CorrespondingAuthorEndpoint public

tobiasBothwellEndpoint : CorrespondingAuthorEndpoint
tobiasBothwellEndpoint = record
  { authorName = "Tobias Bothwell"
  ; email = "tobias.bothwell@colorado.edu"
  ; sourceRole = "corresponding author listed by Nature"
  }

junYeEndpoint : CorrespondingAuthorEndpoint
junYeEndpoint = record
  { authorName = "Jun Ye"
  ; email = "ye@jila.colorado.edu"
  ; sourceRole = "corresponding author listed by Nature"
  }

canonicalCorrespondingAuthorEndpoints : List CorrespondingAuthorEndpoint
canonicalCorrespondingAuthorEndpoints =
  tobiasBothwellEndpoint ∷ junYeEndpoint ∷ []

record AcquisitionEvidenceItem : Set where
  field
    evidenceField : Request.EmpiricalRedshiftEvidenceField
    itemLabel : String
    requestedPayload : String
    deliveryNeededFromAuthors : Bool
    repositoryComputesAfterDelivery : Bool
    publicSummaryAlreadyPresent : Bool

open AcquisitionEvidenceItem public

sourceArtifactBytesRequest : AcquisitionEvidenceItem
sourceArtifactBytesRequest = record
  { evidenceField = Request.sourceArtifactSha256Field
  ; itemLabel = "immutable experiment/data artifact bytes"
  ; requestedPayload =
      "exact versioned byte artifact for the experimental dataset and/or authoritative export; DASHI computes SHA-256 after acquisition"
  ; deliveryNeededFromAuthors = true
  ; repositoryComputesAfterDelivery = true
  ; publicSummaryAlreadyPresent = false
  }

rawMeasurementRequest : AcquisitionEvidenceItem
rawMeasurementRequest = record
  { evidenceField = Request.rawMeasurementField
  ; itemLabel = "raw/fitted measurement payload"
  ; requestedPayload =
      "the fourteen fitted gradients with run identifiers, fit weights, position-resolved clock-frequency data or the authoritative export from which those gradients were fitted"
  ; deliveryNeededFromAuthors = true
  ; repositoryComputesAfterDelivery = false
  ; publicSummaryAlreadyPresent = true
  }

rawUncertaintyRequest : AcquisitionEvidenceItem
rawUncertaintyRequest = record
  { evidenceField = Request.rawUncertaintyField
  ; itemLabel = "per-run and fit uncertainty payload"
  ; requestedPayload =
      "statistical uncertainty for each fitted gradient, weighting convention, confidence convention, and the numerical inputs used to obtain the reported combined uncertainty"
  ; deliveryNeededFromAuthors = true
  ; repositoryComputesAfterDelivery = false
  ; publicSummaryAlreadyPresent = true
  }

fullSystematicsRequest : AcquisitionEvidenceItem
fullSystematicsRequest = record
  { evidenceField = Request.systematicsBudgetField
  ; itemLabel = "replayable systematic-correction inputs"
  ; requestedPayload =
      "machine-readable systematic corrections and uncertainties used for the final gradient, including the inputs behind the published systematic summary"
  ; deliveryNeededFromAuthors = true
  ; repositoryComputesAfterDelivery = false
  ; publicSummaryAlreadyPresent = true
  }

covarianceRequest : AcquisitionEvidenceItem
covarianceRequest = record
  { evidenceField = Request.covarianceOrIndependenceField
  ; itemLabel = "covariance / independence treatment"
  ; requestedPayload =
      "covariance matrix for fitted and systematic terms, or the exact independence assumptions and combination rule used when a full covariance matrix was not retained"
  ; deliveryNeededFromAuthors = true
  ; repositoryComputesAfterDelivery = false
  ; publicSummaryAlreadyPresent = false
  }

canonicalAuthorEvidenceRequests : List AcquisitionEvidenceItem
canonicalAuthorEvidenceRequests =
  sourceArtifactBytesRequest
  ∷ rawMeasurementRequest
  ∷ rawUncertaintyRequest
  ∷ fullSystematicsRequest
  ∷ covarianceRequest
  ∷ []

record AnalysisCodeRequest : Set where
  field
    requestLabel : String
    requestedPayload : String
    authorSupplied : Bool
    authorSuppliedIsTrue : authorSupplied ≡ true

open AnalysisCodeRequest public

canonicalAnalysisCodeRequest : AnalysisCodeRequest
canonicalAnalysisCodeRequest = record
  { requestLabel = "analysis code and reproducible execution identity"
  ; requestedPayload =
      "analysis code used for the reported gradients, exact revision/commit or archive version, dependency/environment information, and the entry point needed to replay the published fit"
  ; authorSupplied = true
  ; authorSuppliedIsTrue = refl
  }

------------------------------------------------------------------------
-- Publicly paid coordinates are not redundantly pushed back onto the authors.
------------------------------------------------------------------------

record AlreadyPaidPublicCoordinates : Set where
  field
    sourceArtifactIdentityAlreadyPaid : Bool
    sourceArtifactIdentityAlreadyPaidIsTrue :
      sourceArtifactIdentityAlreadyPaid ≡ true

    sourceAccessDateAlreadyPaid : Bool
    sourceAccessDateAlreadyPaidIsTrue :
      sourceAccessDateAlreadyPaid ≡ true

    gravitationalPotentialModelAlreadyPaid : Bool
    gravitationalPotentialModelAlreadyPaidIsTrue :
      gravitationalPotentialModelAlreadyPaid ≡ true

    publishedSystematicsSummaryAlreadyPaid : Bool
    publishedSystematicsSummaryAlreadyPaidIsTrue :
      publishedSystematicsSummaryAlreadyPaid ≡ true

open AlreadyPaidPublicCoordinates public

canonicalAlreadyPaidPublicCoordinates : AlreadyPaidPublicCoordinates
canonicalAlreadyPaidPublicCoordinates = record
  { sourceArtifactIdentityAlreadyPaid = true
  ; sourceArtifactIdentityAlreadyPaidIsTrue = refl
  ; sourceAccessDateAlreadyPaid = true
  ; sourceAccessDateAlreadyPaidIsTrue = refl
  ; gravitationalPotentialModelAlreadyPaid = true
  ; gravitationalPotentialModelAlreadyPaidIsTrue = refl
  ; publishedSystematicsSummaryAlreadyPaid = true
  ; publishedSystematicsSummaryAlreadyPaidIsTrue = refl
  }

------------------------------------------------------------------------
-- Post-acquisition work belongs to DASHI, not the corresponding authors.
------------------------------------------------------------------------

record InternalPostAcquisitionWork : Set where
  field
    byteChecksumComputedAfterAcquisition : Bool
    byteChecksumComputedAfterAcquisitionIsFalse :
      byteChecksumComputedAfterAcquisition ≡ false

    analysisReplayCompleted : Bool
    analysisReplayCompletedIsFalse : analysisReplayCompleted ≡ false

    siUnitBindingRevalidated : Bool
    siUnitBindingRevalidatedIsFalse : siUnitBindingRevalidated ≡ false

    consumerIngestionIsInternalPostAcquisition : Bool
    consumerIngestionIsInternalPostAcquisitionIsTrue :
      consumerIngestionIsInternalPostAcquisition ≡ true

    consumerIngestionReceiptConstructed : Bool
    consumerIngestionReceiptConstructedIsFalse :
      consumerIngestionReceiptConstructed ≡ false

open InternalPostAcquisitionWork public

canonicalInternalPostAcquisitionWork : InternalPostAcquisitionWork
canonicalInternalPostAcquisitionWork = record
  { byteChecksumComputedAfterAcquisition = false
  ; byteChecksumComputedAfterAcquisitionIsFalse = refl
  ; analysisReplayCompleted = false
  ; analysisReplayCompletedIsFalse = refl
  ; siUnitBindingRevalidated = false
  ; siUnitBindingRevalidatedIsFalse = refl
  ; consumerIngestionIsInternalPostAcquisition = true
  ; consumerIngestionIsInternalPostAcquisitionIsTrue = refl
  ; consumerIngestionReceiptConstructed = false
  ; consumerIngestionReceiptConstructedIsFalse = refl
  }

record BothwellYe2022ExternalAcquisitionMaxCut : Set where
  field
    genericRequest : Request.QuantumClockEmpiricalRedshiftReceiptRequest
    genericRequestIsCanonical :
      genericRequest ≡ Request.canonicalQuantumClockEmpiricalRedshiftReceiptRequest

    publicArtifactLocator : Locator.PublicExperimentArtifactLocator
    publicArtifactLocatorIsCanonical :
      publicArtifactLocator ≡ Locator.canonicalBothwellYe2022PublicArtifactLocator

    geodeticCalibration : Geodetic.BothwellYe2022GeodeticCalibrationReceipt
    geodeticCalibrationIsCanonical :
      geodeticCalibration ≡ Geodetic.canonicalBothwellYe2022GeodeticCalibrationReceipt

    contacts : List CorrespondingAuthorEndpoint
    authorEvidenceRequests : List AcquisitionEvidenceItem
    codeRequest : AnalysisCodeRequest
    alreadyPaid : AlreadyPaidPublicCoordinates
    internalPostAcquisition : InternalPostAcquisitionWork

    requestPacketConstructed : Bool
    requestPacketConstructedIsTrue : requestPacketConstructed ≡ true

    requestPacketIsEvidence : Bool
    requestPacketIsEvidenceIsFalse : requestPacketIsEvidence ≡ false

    authorRequestSent : Bool
    authorRequestSentIsFalse : authorRequestSent ≡ false

    authorReplyReceived : Bool
    authorReplyReceivedIsFalse : authorReplyReceived ≡ false

    rawExperimentArraysAcquired : Bool
    rawExperimentArraysAcquiredIsFalse : rawExperimentArraysAcquired ≡ false

    analysisCodeAcquired : Bool
    analysisCodeAcquiredIsFalse : analysisCodeAcquired ≡ false

    genericAcceptanceTokenConstructed : Bool
    genericAcceptanceTokenConstructedIsFalse :
      genericAcceptanceTokenConstructed ≡ false

    reading : List String

open BothwellYe2022ExternalAcquisitionMaxCut public

canonicalBothwellYe2022ExternalAcquisitionMaxCut :
  BothwellYe2022ExternalAcquisitionMaxCut
canonicalBothwellYe2022ExternalAcquisitionMaxCut = record
  { genericRequest = Request.canonicalQuantumClockEmpiricalRedshiftReceiptRequest
  ; genericRequestIsCanonical = refl
  ; publicArtifactLocator = Locator.canonicalBothwellYe2022PublicArtifactLocator
  ; publicArtifactLocatorIsCanonical = refl
  ; geodeticCalibration = Geodetic.canonicalBothwellYe2022GeodeticCalibrationReceipt
  ; geodeticCalibrationIsCanonical = refl
  ; contacts = canonicalCorrespondingAuthorEndpoints
  ; authorEvidenceRequests = canonicalAuthorEvidenceRequests
  ; codeRequest = canonicalAnalysisCodeRequest
  ; alreadyPaid = canonicalAlreadyPaidPublicCoordinates
  ; internalPostAcquisition = canonicalInternalPostAcquisitionWork
  ; requestPacketConstructed = true
  ; requestPacketConstructedIsTrue = refl
  ; requestPacketIsEvidence = false
  ; requestPacketIsEvidenceIsFalse = refl
  ; authorRequestSent = false
  ; authorRequestSentIsFalse = refl
  ; authorReplyReceived = false
  ; authorReplyReceivedIsFalse = refl
  ; rawExperimentArraysAcquired = false
  ; rawExperimentArraysAcquiredIsFalse = refl
  ; analysisCodeAcquired = false
  ; analysisCodeAcquiredIsFalse = refl
  ; genericAcceptanceTokenConstructed = false
  ; genericAcceptanceTokenConstructedIsFalse = refl
  ; reading =
      "The remaining external wall is now an explicit author-acquisition packet rather than an untyped roadmap item."
      ∷ "Authors are asked only for evidence that is not already paid publicly: exact dataset bytes, fourteen fitted gradients/position-resolved data, uncertainty/weights, replayable systematics, covariance or independence treatment, and analysis code/version."
      ∷ "Artifact hashing, analysis replay, SI revalidation and the consumer ingestion receipt are repository responsibilities after acquisition."
      ∷ "Constructing this packet neither sends correspondence nor constitutes evidence receipt, acceptance or promotion."
      ∷ []
  }

canonicalAcquisitionPacketConstructed :
  requestPacketConstructed canonicalBothwellYe2022ExternalAcquisitionMaxCut ≡ true
canonicalAcquisitionPacketConstructed = refl

canonicalAcquisitionPacketNotEvidence :
  requestPacketIsEvidence canonicalBothwellYe2022ExternalAcquisitionMaxCut ≡ false
canonicalAcquisitionPacketNotEvidence = refl

canonicalAuthorRequestNotSent :
  authorRequestSent canonicalBothwellYe2022ExternalAcquisitionMaxCut ≡ false
canonicalAuthorRequestNotSent = refl
