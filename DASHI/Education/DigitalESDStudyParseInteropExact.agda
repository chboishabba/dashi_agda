module DASHI.Education.DigitalESDStudyParseInteropExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDManuscriptMethodologyExact as Method
import DASHI.Education.DigitalESDStudyClaimMethodBridgeExact as ClaimMethod
import DASHI.Education.DigitalESDReviewedUnresolvedRoutingExact as Routing
import DASHI.Education.DigitalESDSourceAuditAdmissionExact as Audit
import DASHI.Education.DigitalESDSLRSourceReviewBridgeExact as SLR

------------------------------------------------------------------------
-- DIGITAL-ESD FULL-TEXT PARSE INTEROP
--
-- Runtime wrappers:
--
--   interop_scripts/digital_esd/prepare_slr_source_units.py
--   interop_scripts/digital_esd/run_slr_source_unit_parse.py
--   interop_scripts/digital_esd/compile_study_extraction_packets.py
--
-- Existing generic parser:
--
--   tools/slr-discourse-reconstruct/slr_source_unit_pnf_batch.py
--
-- The parser remains candidate-only.  This owner records the application
-- projection from retained full text into the existing 19-coordinate Digital-
-- ESD extraction schema.  Parser evidence nominates spans; review pays
-- coordinates.  Screening-resolution full text remains a separate lane.
------------------------------------------------------------------------

baseExtractionCoordinateCount : Nat
baseExtractionCoordinateCount = Method.extractionCoordinateCount

effectiveExtractionCoordinateCount : Nat
effectiveExtractionCoordinateCount = ClaimMethod.effectiveExtractionCoordinateCount

record GenericSLRParseReceipt : Set where
  constructor generic-slr-parse-receipt
  field
    sourceIdentityReference : String
    sourceUnitReference : String
    sourceRevisionReference : String
    sourceTextSha256 : String
    parserDocumentReference : String
    parserModelReference : String
    parserVersionReference : String
    pnfCandidateCount : Nat

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    semanticPromotion : Bool
    semanticPromotionIsFalse : semanticPromotion ≡ false

    parserCreatesClaimTruth : Bool
    parserCreatesClaimTruthIsFalse : parserCreatesClaimTruth ≡ false

open GenericSLRParseReceipt public

data ParseLane : Set where
  retainedStudyAuditLane : ParseLane
  screeningResolutionLane : ParseLane

record ExtractionCoordinateCandidate : Set where
  constructor extraction-coordinate-candidate
  field
    coordinateReference : String
    candidateSpanCount : Nat
    candidateEvidenceReference : String

    coordinatePaid : Bool
    coordinatePaidIsFalse : coordinatePaid ≡ false

    reviewRequired : Bool
    reviewRequiredIsTrue : reviewRequired ≡ true

    automaticAbsenceInference : Bool
    automaticAbsenceInferenceIsFalse :
      automaticAbsenceInference ≡ false

open ExtractionCoordinateCandidate public

record ParsedRetainedStudyPacket : Set where
  constructor parsed-retained-study-packet
  field
    parseReceipt : GenericSLRParseReceipt
    extractionCoordinateCount : Nat
    extractionCoordinateCountIsNineteen :
      extractionCoordinateCount ≡ baseExtractionCoordinateCount

    claimCeilingCoordinateIncluded : Bool
    claimCeilingCoordinateIncludedIsTrue :
      claimCeilingCoordinateIncluded ≡ true

    predicateNormalFormOverlayIncluded : Bool
    predicateNormalFormOverlayIncludedIsTrue :
      predicateNormalFormOverlayIncluded ≡ true

    intersectionalAbsenceOverlayRequired : Bool
    intersectionalAbsenceOverlayRequiredIsTrue :
      intersectionalAbsenceOverlayRequired ≡ true

    materialEnvironmentalOverlayRequired : Bool
    materialEnvironmentalOverlayRequiredIsTrue :
      materialEnvironmentalOverlayRequired ≡ true

    parserPaysAnyCoordinate : Bool
    parserPaysAnyCoordinateIsFalse :
      parserPaysAnyCoordinate ≡ false

    sourceAuditAdmissionCreated : Bool
    sourceAuditAdmissionCreatedIsFalse :
      sourceAuditAdmissionCreated ≡ false

open ParsedRetainedStudyPacket public

record ParsedScreeningResolutionPacket : Set where
  constructor parsed-screening-resolution-packet
  field
    parseReceipt : GenericSLRParseReceipt
    routingReference : String

    purposeIsScreeningResolution : Bool
    purposeIsScreeningResolutionIsTrue :
      purposeIsScreeningResolution ≡ true

    createsStudyAuditPacket : Bool
    createsStudyAuditPacketIsFalse :
      createsStudyAuditPacket ≡ false

    createsInclusion : Bool
    createsInclusionIsFalse :
      createsInclusion ≡ false

    createsExclusion : Bool
    createsExclusionIsFalse :
      createsExclusion ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open ParsedScreeningResolutionPacket public

record StudyParseInteropBoundary : Set where
  constructor study-parse-interop-boundary
  field
    reusesGenericSLRParser : Bool
    reusesGenericSLRParserIsTrue :
      reusesGenericSLRParser ≡ true

    digitalESDParserForkCreated : Bool
    digitalESDParserForkCreatedIsFalse :
      digitalESDParserForkCreated ≡ false

    retainedStudyLaneDistinctFromResolutionLane : Bool
    retainedStudyLaneDistinctFromResolutionLaneIsTrue :
      retainedStudyLaneDistinctFromResolutionLane ≡ true

    parsesSentenceBoundedPNFCandidates : Bool
    parsesSentenceBoundedPNFCandidatesIsTrue :
      parsesSentenceBoundedPNFCandidates ≡ true

    preservesSourceRevisionAndTextHash : Bool
    preservesSourceRevisionAndTextHashIsTrue :
      preservesSourceRevisionAndTextHash ≡ true

    parserTextDigestMatchesVerifiedFullText : Bool
    parserTextDigestMatchesVerifiedFullTextIsTrue :
      parserTextDigestMatchesVerifiedFullText ≡ true

    projectsOntoExistingNineteenCoordinateSchema : Bool
    projectsOntoExistingNineteenCoordinateSchemaIsTrue :
      projectsOntoExistingNineteenCoordinateSchema ≡ true

    parserMayPayExtractionCoordinate : Bool
    parserMayPayExtractionCoordinateIsFalse :
      parserMayPayExtractionCoordinate ≡ false

    parserMayRaiseClaimCeiling : Bool
    parserMayRaiseClaimCeilingIsFalse :
      parserMayRaiseClaimCeiling ≡ false

    parserMayCreateSourceAuditAdmission : Bool
    parserMayCreateSourceAuditAdmissionIsFalse :
      parserMayCreateSourceAuditAdmission ≡ false

    unreportedDemographicsMayBecomeAbsenceFact : Bool
    unreportedDemographicsMayBecomeAbsenceFactIsFalse :
      unreportedDemographicsMayBecomeAbsenceFact ≡ false

    genericInfrastructureAverageMayBecomeStudyFootprint : Bool
    genericInfrastructureAverageMayBecomeStudyFootprintIsFalse :
      genericInfrastructureAverageMayBecomeStudyFootprint ≡ false

open StudyParseInteropBoundary public

canonicalStudyParseInteropBoundary : StudyParseInteropBoundary
canonicalStudyParseInteropBoundary =
  study-parse-interop-boundary
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

claimMethodBoundary : ClaimMethod.StudyClaimMethodBoundary
claimMethodBoundary = ClaimMethod.canonicalStudyClaimMethodBoundary

reviewedUnresolvedBoundary : Routing.ReviewedUnresolvedRoutingBoundary
reviewedUnresolvedBoundary = Routing.canonicalReviewedUnresolvedRoutingBoundary

sourceAuditBoundary : Audit.SourceAuditAdmissionBoundary
sourceAuditBoundary = Audit.canonicalSourceAuditAdmissionBoundary

slrBridgeBoundary : SLR.DigitalESDSLRBridgeBoundary
slrBridgeBoundary = SLR.canonicalDigitalESDSLRBridgeBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ScreeningResolutionParseCreatesStudyAuditPacket : Set where
data ParserOutputCreatesSourceAuditAdmission : Set where
data ParserOutputRaisesStudyClaimCeiling : Set where
data ParserOutputCreatesClaimTruth : Set where
data ParserOutputPaysExtractionCoordinate : Set where
data ParserInfersAbsentGroupFromUnreportedDemographics : Set where
data ParserCreatesDeploymentFootprintFromGenericInfrastructure : Set where

screeningResolutionParseDoesNotCreateStudyAuditPacket :
  ScreeningResolutionParseCreatesStudyAuditPacket → ⊥
screeningResolutionParseDoesNotCreateStudyAuditPacket ()

parserOutputDoesNotCreateSourceAuditAdmission :
  ParserOutputCreatesSourceAuditAdmission → ⊥
parserOutputDoesNotCreateSourceAuditAdmission ()

parserOutputDoesNotRaiseStudyClaimCeiling :
  ParserOutputRaisesStudyClaimCeiling → ⊥
parserOutputDoesNotRaiseStudyClaimCeiling ()

parserOutputDoesNotCreateClaimTruth :
  ParserOutputCreatesClaimTruth → ⊥
parserOutputDoesNotCreateClaimTruth ()

parserOutputDoesNotPayExtractionCoordinate :
  ParserOutputPaysExtractionCoordinate → ⊥
parserOutputDoesNotPayExtractionCoordinate ()

parserDoesNotInferAbsentGroupFromUnreportedDemographics :
  ParserInfersAbsentGroupFromUnreportedDemographics → ⊥
parserDoesNotInferAbsentGroupFromUnreportedDemographics ()

parserDoesNotCreateDeploymentFootprintFromGenericInfrastructure :
  ParserCreatesDeploymentFootprintFromGenericInfrastructure → ⊥
parserDoesNotCreateDeploymentFootprintFromGenericInfrastructure ()

studyParseInteropReading : String
studyParseInteropReading =
  "Digital-ESD retained full texts are parsed by the existing generic SLR source-unit dependency/PNF parser through a thin application adapter. The parser emits sentence-bounded candidate observations with exact revision and source-text hashes. A Digital-ESD compiler projects those candidates onto the existing nineteen-coordinate manuscript extraction schema, plus the separate study-claim-ceiling coordinate and required PNF, intersectional-absence and material/environmental overlays. Automatic parsing only nominates source spans; it pays no extraction coordinate, raises no claim ceiling and creates no SourceAuditAdmission. Full text obtained solely to resolve an explicitly reviewed unresolved screening decision stays in the screening-resolution lane and cannot become a retained-study audit packet without a later explicit include/probable decision."
