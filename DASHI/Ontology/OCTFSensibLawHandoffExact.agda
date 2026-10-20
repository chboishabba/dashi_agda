module DASHI.Ontology.OCTFSensibLawHandoffExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SOURCE OWNERS
--
-- Provenance strata remain distinct:
--   * Rosario published research;
--   * Ege Doğan / Peter Patel-Schneider published disjointness work;
--   * OCTF meeting/course records;
--   * SensibLaw/ITIR handoff and execution-governance documents;
--   * DASHI formal reconstruction.
--
-- Meeting minutes are evidence of what participants reported/discussed, not a
-- publication-level theorem. SensibLaw's description of another author's work
-- is a handoff/prior-art receipt, not a replacement for that publication.
------------------------------------------------------------------------

data SourceOwner : Set where
  rosarioPublishedResearch : SourceOwner
  peterEgePublishedResearch : SourceOwner
  octfMeetingMinutes : SourceOwner
  octfCourseMaterial : SourceOwner
  sensibLawHandoffDocs : SourceOwner
  dashiFormalReconstruction : SourceOwner

------------------------------------------------------------------------
-- LAST-YEAR OCTF / COURSE RECEIPTS REVIEWED FOR THIS TRANCHE
------------------------------------------------------------------------

data OCTFMeetingClaim : Set where
  march2026RosarioEightDomainsHotspots : OCTFMeetingClaim
  march2026RosarioInverseInheritanceTests : OCTFMeetingClaim
  march2026RosarioCrossModelLowConsistencyHotspot : OCTFMeetingClaim
  march2026GNUProjectLinuxExample : OCTFMeetingClaim
  march2026PlanToReviewDomainAndEventuallyChange : OCTFMeetingClaim
  may2026JohlMultipleSourceKinds : OCTFMeetingClaim
  may2026NaturalLanguageNeedsLogicalTranslation : OCTFMeetingClaim
  may2026WikipediaInfoboxesAsSource : OCTFMeetingClaim
  may2026PeterDisjointnessFollowthrough : OCTFMeetingClaim
  june2026LLMCheckingOntologyRelationships : OCTFMeetingClaim
  june2026ReferencesCanRecordLLMAndSourceSnaks : OCTFMeetingClaim
  august2026MetaclassBestPractices : OCTFMeetingClaim
  august2026EgeDisjointnessUnderused : OCTFMeetingClaim
  august2026EgeGameForOntologyWork : OCTFMeetingClaim
  september2026RoundtableGamifiedFixing : OCTFMeetingClaim
  october2026OntologiesAndGenerativeAI : OCTFMeetingClaim
  course2026RosarioSemanticFailuresImproveWikidata : OCTFMeetingClaim

------------------------------------------------------------------------
-- SENSIBLAW HANDOFF / CLIMATE / NAT RECEIPTS
------------------------------------------------------------------------

data SensibLawHandoffClaim : Set where
  boundedSliceBeforeAction : SensibLawHandoffClaim
  classifyIntoExplicitBuckets : SensibLawHandoffClaim
  reviewerFacingPackBeforeStaging : SensibLawHandoffClaim
  onlyCheckedSafeSubsetStages : SensibLawHandoffClaim
  verifyAfterEdit : SensibLawHandoffClaim
  llmSuggestionIsCandidateSignal : SensibLawHandoffClaim
  externalOntologySignalIsCandidateSignal : SensibLawHandoffClaim
  peterDisjointnessReviewLane : SensibLawHandoffClaim
  egePairwiseDisjointnessExtractionLane : SensibLawHandoffClaim
  rosarioHotspotBenchmarkLane : SensibLawHandoffClaim
  climateMigrationUsesFullStatementBundle : SensibLawHandoffClaim
  climateMigrationIsNotPropertyRename : SensibLawHandoffClaim
  climateMigrationHasSplitAndAbstainBuckets : SensibLawHandoffClaim
  natMoonshotIsBlindMigrationAutomation : SensibLawHandoffClaim
  natCurrentPostureReviewFirst : SensibLawHandoffClaim
  natCurrentPostureSplitFirst : SensibLawHandoffClaim
  natCurrentPostureFailClosed : SensibLawHandoffClaim
  natNoLiveWriteVerificationYet : SensibLawHandoffClaim
  candidateComparisonIsReviewOnly : SensibLawHandoffClaim

------------------------------------------------------------------------
-- ROLE CROSSWALK
------------------------------------------------------------------------

data AssistLane : Set where
  natMigrationLane : AssistLane
  peterEgeDisjointnessLane : AssistLane
  rosarioHotspotLane : AssistLane
  johlPNFReviewLane : AssistLane
  climateMigrationLane : AssistLane

data ReviewDisposition : Set where
  candidateOnly : ReviewDisposition
  reviewable : ReviewDisposition
  held : ReviewDisposition
  promotable : ReviewDisposition
  abstain : ReviewDisposition

initialDisposition : AssistLane → ReviewDisposition
initialDisposition natMigrationLane = held
initialDisposition peterEgeDisjointnessLane = reviewable
initialDisposition rosarioHotspotLane = candidateOnly
initialDisposition johlPNFReviewLane = reviewable
initialDisposition climateMigrationLane = reviewable

currentNatLiveDisposition : ReviewDisposition
currentNatLiveDisposition = held

------------------------------------------------------------------------
-- ATTRIBUTION OWNER FOR EACH LAYER
------------------------------------------------------------------------

data HandoffLayer : Set where
  rosarioPaperMethodLayer : HandoffLayer
  rosarioMeetingContinuationLayer : HandoffLayer
  peterEgePublishedDisjointnessLayer : HandoffLayer
  peterEgeSensibLawReviewHandoffLayer : HandoffLayer
  natAutomationPostureLayer : HandoffLayer
  climateMigrationProtocolLayer : HandoffLayer
  pnfAdmissibilityFactorisationLayer : HandoffLayer

ownerOfLayer : HandoffLayer → SourceOwner
ownerOfLayer rosarioPaperMethodLayer = rosarioPublishedResearch
ownerOfLayer rosarioMeetingContinuationLayer = octfMeetingMinutes
ownerOfLayer peterEgePublishedDisjointnessLayer = peterEgePublishedResearch
ownerOfLayer peterEgeSensibLawReviewHandoffLayer = sensibLawHandoffDocs
ownerOfLayer natAutomationPostureLayer = sensibLawHandoffDocs
ownerOfLayer climateMigrationProtocolLayer = sensibLawHandoffDocs
ownerOfLayer pnfAdmissibilityFactorisationLayer = dashiFormalReconstruction

------------------------------------------------------------------------
-- SOURCE RECEIPT LOCATORS
------------------------------------------------------------------------

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    owner : SourceOwner
    locator : String
    reading : String

open SourceReceipt public

peterEgePublishedReceipt : SourceReceipt
peterEgePublishedReceipt =
  sourceReceipt
    peterEgePublishedResearch
    "Ege Doğan and Peter F. Patel-Schneider, Disjointness Violations in Wikidata; SensibLaw prior-art copy 2410.13707v2_ege.pdf"
    "published prior art for Wikidata disjointness violations, pairwise disjoint-class extraction and culprit-oriented analysis; SensibLaw does not claim full method parity"

rosarioMarch2026MeetingReceipt : SourceReceipt
rosarioMarch2026MeetingReceipt =
  sourceReceipt
    octfMeetingMinutes
    "Wikidata Ontology Cleaning Task Force meeting notes, 24 March 2026"
    "Rosario reports eight-domain LLM/Wikidata hotspot work, inverse/inheritance checks, cross-model controversy and eventual review/change intent"

johlMay2026MeetingReceipt : SourceReceipt
johlMay2026MeetingReceipt =
  sourceReceipt
    octfMeetingMinutes
    "Wikidata Ontology Cleaning Task Force meeting notes, 12 May 2026"
    "SensibLaw/ITIR follow-up: multiple source kinds, logical translation for natural language, infoboxes, and Peter follow-through on disjointness"

june2026MeetingReceipt : SourceReceipt
june2026MeetingReceipt =
  sourceReceipt
    octfMeetingMinutes
    "Wikidata Ontology Cleaning Task Force meeting notes, 16 June 2026"
    "LLM checking of ontology relationships; references may record which LLM was used plus source information as separate snaks"

rosarioCourse2026Receipt : SourceReceipt
rosarioCourse2026Receipt =
  sourceReceipt
    octfCourseMaterial
    "Wikidata Ontology Course Week 5, 4 June 2026"
    "Rosario presentation: Using LLM Semantic Failures to Analyze and Improve Wikidata"

sensibLawEntrypointReceipt : SourceReceipt
sensibLawEntrypointReceipt =
  sourceReceipt
    sensibLawHandoffDocs
    "SensibLaw docs/planning/wikidata_octf_entrypoint_20260421.md"
    "bounded review/check layer; signals from constraints, LLMs, external scaffolds or sync tools do not become edit authority"

sensibLawClimateReceipt : SourceReceipt
sensibLawClimateReceipt =
  sourceReceipt
    sensibLawHandoffDocs
    "SensibLaw docs/planning/wikidata_climate_change_property_migration_protocol_20260327.md"
    "review-first property migration over complete statement bundles with split, manual-review and abstention outcomes"

sensibLawNatReceipt : SourceReceipt
sensibLawNatReceipt =
  sourceReceipt
    sensibLawHandoffDocs
    "SensibLaw docs/wikidata_working_group_status.md"
    "Nat moonshot is blind automation, while present lane remains review-first, split-first, fail-closed and without claimed live-write verification"

------------------------------------------------------------------------
-- SIGNAL / REVIEW / EDIT AUTHORITY NON-COLLAPSE
------------------------------------------------------------------------

data MeetingSignalTruthPermission : Set where

data HandoffSignalEditPermission : Set where

data ReviewableMeansPromotablePermission : Set where

data PromotableMeansTruthPermission : Set where

meetingSignalCannotPromoteTruth : MeetingSignalTruthPermission → ⊥
meetingSignalCannotPromoteTruth ()

handoffSignalCannotPromoteEditAuthority : HandoffSignalEditPermission → ⊥
handoffSignalCannotPromoteEditAuthority ()

reviewableCannotAutoPromote : ReviewableMeansPromotablePermission → ⊥
reviewableCannotAutoPromote ()

promotableCannotAssertTruth : PromotableMeansTruthPermission → ⊥
promotableCannotAssertTruth ()

------------------------------------------------------------------------
-- PARALLEL ASSIST-LANE CROSSWALK
--
-- This is DASHI's local organizational crosswalk of the documented handoff.
-- It is not a claim that collaborators endorsed this exact decomposition.
------------------------------------------------------------------------

data AssistContribution : Set where
  disjointnessConstraintEvidence : AssistContribution
  pairwiseViolationExtraction : AssistContribution
  llmHotspotEvidence : AssistContribution
  multiSourceLogicalEvidence : AssistContribution
  statementBundleMigrationEvidence : AssistContribution
  pnfResidualGovernance : AssistContribution

laneContribution : AssistLane → AssistContribution
laneContribution natMigrationLane = statementBundleMigrationEvidence
laneContribution peterEgeDisjointnessLane = disjointnessConstraintEvidence
laneContribution rosarioHotspotLane = llmHotspotEvidence
laneContribution johlPNFReviewLane = pnfResidualGovernance
laneContribution climateMigrationLane = statementBundleMigrationEvidence

------------------------------------------------------------------------
-- STATUS
------------------------------------------------------------------------

record OCTFHandoffStatus : Set where
  constructor octfHandoffStatus
  field
    sourceOwnersRemainDistinct : Bool
    paperMeetingAndRepoClaimsSeparated : Bool
    peterEgePublicationSeparatedFromHandoff : Bool
    reviewFirstBoundaryPreserved : Bool
    natMoonshotNotCurrentAuthority : Bool
    llmSignalsRemainCandidateEvidence : Bool
    disjointnessLaneRemainsReviewSupport : Bool
    climateMigrationPreservesBundles : Bool
    pnfCrossPollinationAttributedToDASHI : Bool

    sourceOwnersRemainDistinctIsTrue : sourceOwnersRemainDistinct ≡ true
    paperMeetingAndRepoClaimsSeparatedIsTrue :
      paperMeetingAndRepoClaimsSeparated ≡ true
    peterEgePublicationSeparatedFromHandoffIsTrue :
      peterEgePublicationSeparatedFromHandoff ≡ true
    reviewFirstBoundaryPreservedIsTrue : reviewFirstBoundaryPreserved ≡ true
    natMoonshotNotCurrentAuthorityIsTrue : natMoonshotNotCurrentAuthority ≡ true
    llmSignalsRemainCandidateEvidenceIsTrue :
      llmSignalsRemainCandidateEvidence ≡ true
    disjointnessLaneRemainsReviewSupportIsTrue :
      disjointnessLaneRemainsReviewSupport ≡ true
    climateMigrationPreservesBundlesIsTrue :
      climateMigrationPreservesBundles ≡ true
    pnfCrossPollinationAttributedToDASHIIsTrue :
      pnfCrossPollinationAttributedToDASHI ≡ true

open OCTFHandoffStatus public

canonicalOCTFHandoffStatus : OCTFHandoffStatus
canonicalOCTFHandoffStatus =
  octfHandoffStatus
    true true true true true true true true true
    refl refl refl refl refl refl refl refl refl
