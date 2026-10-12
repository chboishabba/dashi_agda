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

-- March/April 2026 S&P500 specification.  Do not silently treat this as the
-- July revised universe.
canonicalCorporateCorpusReceipt : CorporateCorpusReceipt
canonicalCorporateCorpusReceipt = corporate-corpus-receipt
  52266 1293753 117394 1179 841 841 602 true true

------------------------------------------------------------------------
-- JULY 2026 REVISED UNIVERSE / DEFINITION
--
-- The revised paper broadens the searched population from the earlier S&P500
-- specification to CEOs/directors of U.S. public firms and changes the promoted
-- contact construct to "frequent contact".  The 841 count belongs to this
-- revised threshold/universe.  The early 1,179 direct-contact count and revised
-- 841 frequent-contact count are therefore not alternative labels for one set.
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

-- Retained from the earlier calibration.  Revised-paper mechanism findings
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
    searchFinanceAndTechnologyFirst : Bool
    useMediaCoverageAsCompleteAtlas : Bool
open CorporateAcquisitionPolicy public

canonicalCorporateAcquisitionPolicy : CorporateAcquisitionPolicy
canonicalCorporateAcquisitionPolicy = corporate-acquisition-policy
  true true true true true true false

------------------------------------------------------------------------
-- Attribution / promotion firewalls.
------------------------------------------------------------------------

data LLMLabelCreatesPrimaryReceipt : Set where
data BoardInterlockCreatesPersonalContact : Set where
data NetworkCentralityCreatesWrongdoing : Set where
data FirmAssociationCreatesIndividualCulpability : Set where
data RevisedFrequentContactEqualsBroaderDirectContact : Set where
data RevisedUniverseEqualsEarlySP500Universe : Set where
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
