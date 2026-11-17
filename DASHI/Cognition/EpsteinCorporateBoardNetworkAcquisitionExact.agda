module DASHI.Cognition.EpsteinCorporateBoardNetworkAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- CORPORATE / BOARD-NETWORK ACQUISITION ATLAS
--
-- Source donor: Gertsberg, Pagel, Volkova, CESifo Working Paper 12580,
-- "Him Too? Analyzing the Effects of Epstein Connections" (2026).
--
-- This owner imports the paper as an acquisition/ranking surface only. Its
-- LLM-classified contact labels do not themselves become edge-local DASHI
-- relationship receipts. Individual people/firms must be re-resolved to the
-- underlying DOJ correspondence, meeting record or institutional source.
------------------------------------------------------------------------

record CorporateCorpusReceipt : Set where
  constructor corporate-corpus-receipt
  field
    sp500People2006to2026 : Nat
    textBearingDocuments : Nat
    nameMatchedDocuments : Nat
    broaderDirectContactPeople : Nat
    revisedFrequentContactPeople : Nat
    firmsInPointInTimeUniverse : Nat
    finalAnalyticFirms : Nat
    mediaCoverageUnderCapturesDocumentNetwork : Bool
    directContactDefinitionIncludesEmailOrExplicitMeeting : Bool
open CorporateCorpusReceipt public

-- Cross-version summary retained for compatibility with earlier consumers.
-- 52,266 / 117,394 / 1,179 belong to the March/April S&P500 specification;
-- 841 is the latest July frequent-contact figure and must not be read as if it
-- were produced by the early threshold/universe.
canonicalCorporateCorpusReceipt : CorporateCorpusReceipt
canonicalCorporateCorpusReceipt = corporate-corpus-receipt
  52266 1293753 117394 1179 841 841 602 true true

------------------------------------------------------------------------
-- REVISED UNIVERSE / DEFINITION AND VERSION LINEAGE
------------------------------------------------------------------------

record RevisedCorporateCorpusReceipt : Set where
  constructor revised-corporate-corpus-receipt
  field
    usPublicFirmPeopleSearched : Nat
    revisedFrequentContactDirectors : Nat
    revisedUniverseIsBroaderThanEarlySP500Universe : Bool
    revisedFrequentContactIsSameThresholdAsEarlyDirectContact : Bool
    personLevelPromotionStillRequiresUnderlyingDocument : Bool
open RevisedCorporateCorpusReceipt public

canonicalRevisedCorporateCorpusReceipt : RevisedCorporateCorpusReceipt
canonicalRevisedCorporateCorpusReceipt =
  revised-corporate-corpus-receipt 92698 841 true false true

record CorporateRevisionLineage : Set where
  constructor corporate-revision-lineage
  field
    earlyMarchDirectContactCount : Nat
    intermediateJuneFrequentContactCount : Nat
    latestJulyFrequentContactCount : Nat
    intermediateAndLatestUseSameFrozenDataset : Bool
    latestSupersedesIntermediateForCurrentRouting : Bool
    countsMayBeCollapsedWithoutDateDefinition : Bool
open CorporateRevisionLineage public

canonicalCorporateRevisionLineage : CorporateRevisionLineage
canonicalCorporateRevisionLineage = corporate-revision-lineage
  1179 825 841 false true false

revisionLineageReading : String
revisionLineageReading =
  "March 2026 reported 1,179 direct-contact S&P500 CEOs/directors under an early universe/definition. A 17 June 2026 Bonn seminar abstract reported 825 frequent-contact directors over the expanded approximately 92,698-person U.S.-public-firm search universe. The 21 July revised paper/current author page reports 841 frequent-contact directors. Treat 825->841 as revision lineage, not as simultaneous contradictory counts for one frozen extract; use 841 for current routing and retain 825 as provenance."

record CorporateNetworkResult : Set where
  constructor corporate-network-result
  field
    overallDensityIncreasePercent : Nat
    financeConnectedFirms : Nat
    financeFirmsTotal : Nat
    financeDensityIncreasePercent : Nat
    technologyComponentsBridged : Bool
    networkExpansionMeasured : Bool
    normContagionMeasured : Bool
    causalMechanismUniversallyEstablished : Bool
open CorporateNetworkResult public

-- Retained from the earlier calibration. Revised-paper mechanism findings
-- below supersede any simplistic interpretation that density/centrality itself
-- is the misconduct mechanism.
canonicalCorporateNetworkResult : CorporateNetworkResult
canonicalCorporateNetworkResult = corporate-network-result
  353 32 50 550 true true true false

record RevisedMechanismBoundary : Set where
  constructor revised-mechanism-boundary
  field
    ownNetworkCentralityGainPredictsMisconduct : Bool
    sharedDirectorExposureToEpsteinConnectedBoardsPredictsMisconduct : Bool
    negativeThreeDayMarketReactionMeasured : Bool
    marketReactionPercentMagnitudeAbout37Tenths : Bool
    mechanismTestEstablishesUniversalCausation : Bool
open RevisedMechanismBoundary public

canonicalRevisedMechanismBoundary : RevisedMechanismBoundary
canonicalRevisedMechanismBoundary = revised-mechanism-boundary
  false true true true false

------------------------------------------------------------------------
-- Acquisition interpretation.
------------------------------------------------------------------------

record CorporateAcquisitionPolicy : Set where
  constructor corporate-acquisition-policy
  field
    ingestRankedCorporateCandidates : Bool
    resolveEveryPromotedPersonToUnderlyingDocument : Bool
    preserveMentionVsContactDistinction : Bool
    preserveContactVsWrongdoingDistinction : Bool
    preserveVersionSpecificThresholds : Bool
    preserveIntermediateRevisionCounts : Bool
    searchFinanceAndTechnologyFirst : Bool
    useMediaCoverageAsCompleteAtlas : Bool
open CorporateAcquisitionPolicy public

canonicalCorporateAcquisitionPolicy : CorporateAcquisitionPolicy
canonicalCorporateAcquisitionPolicy = corporate-acquisition-policy
  true true true true true true true false

------------------------------------------------------------------------
-- Attribution / promotion firewalls.
------------------------------------------------------------------------

data LLMLabelCreatesPrimaryReceipt : Set where
data BoardInterlockCreatesPersonalContact : Set where
data NetworkCentralityCreatesWrongdoing : Set where
data FirmAssociationCreatesIndividualCulpability : Set where
data RevisedFrequentContactEqualsBroaderDirectContact : Set where
data RevisedUniverseEqualsEarlySP500Universe : Set where
data IntermediateCountEqualsLatestCount : Set where
data NetworkDensityCreatesIndividualBenefit : Set where
data MarketReactionCreatesWrongdoing : Set where

llmLabelDoesNotCreatePrimaryReceipt : LLMLabelCreatesPrimaryReceipt → ⊥
llmLabelDoesNotCreatePrimaryReceipt ()

boardInterlockDoesNotCreatePersonalContact : BoardInterlockCreatesPersonalContact → ⊥
boardInterlockDoesNotCreatePersonalContact ()

networkCentralityDoesNotCreateWrongdoing : NetworkCentralityCreatesWrongdoing → ⊥
networkCentralityDoesNotCreateWrongdoing ()

firmAssociationDoesNotCreateIndividualCulpability :
  FirmAssociationCreatesIndividualCulpability → ⊥
firmAssociationDoesNotCreateIndividualCulpability ()

versionThresholdsMustNotBeCollapsed :
  RevisedFrequentContactEqualsBroaderDirectContact → ⊥
versionThresholdsMustNotBeCollapsed ()

versionUniversesMustNotBeCollapsed :
  RevisedUniverseEqualsEarlySP500Universe → ⊥
versionUniversesMustNotBeCollapsed ()

intermediateAndLatestCountsMustNotBeCollapsed : IntermediateCountEqualsLatestCount → ⊥
intermediateAndLatestCountsMustNotBeCollapsed ()

networkDensityDoesNotCreateIndividualBenefit : NetworkDensityCreatesIndividualBenefit → ⊥
networkDensityDoesNotCreateIndividualBenefit ()

marketReactionDoesNotCreateWrongdoing : MarketReactionCreatesWrongdoing → ⊥
marketReactionDoesNotCreateWrongdoing ()

------------------------------------------------------------------------
-- Ellison / broad-tech boundary from current public-source round.
------------------------------------------------------------------------

record EllisonCurrentBoundary : Set where
  constructor ellison-current-boundary
  field
    blackBookListingReported : Bool
    threePhoneNumbersReported : Bool
    flightAppearanceEstablished : Bool
    directEmailEstablished : Bool
    personalRelationshipEstablished : Bool
    mediaInfrastructureRelevance : Bool
    wrongdoingEstablished : Bool
open EllisonCurrentBoundary public

canonicalEllisonCurrentBoundary : EllisonCurrentBoundary
canonicalEllisonCurrentBoundary = ellison-current-boundary
  true true false false false true false

------------------------------------------------------------------------
-- Finance / tech source hierarchy for the next acquisition round.
------------------------------------------------------------------------

data AcquisitionSurface : Set where
  dojUnderlyingRecord : AcquisitionSurface
  institutionalInvestigation : AcquisitionSurface
  congressionalFinancialInvestigation : AcquisitionSurface
  peerReviewedOrWorkingPaperAtlas : AcquisitionSurface
  highQualityReporting : AcquisitionSurface
  publicCorpusIndex : AcquisitionSurface
  aiGeneratedLeadBundle : AcquisitionSurface

record RoundRule : Set where
  constructor round-rule
  field
    freshWebSweepRequired : Bool
    governmentTransactionAtlasRequired : Bool
    corporateBoardAtlasRequired : Bool
    techRelationshipAtlasRequired : Bool
    underlyingDocumentResolutionRequired : Bool
    aiModeLeadCanPromoteEdgeWithoutVerification : Bool
open RoundRule public

canonicalRoundRule : RoundRule
canonicalRoundRule = round-rule true true true true true false
