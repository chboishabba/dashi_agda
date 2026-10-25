module DASHI.Governance.BOMFordhamMediaClaimAuditExact where

-- Case-specific source and claim audit, 24 October 2026.
-- DASHI owns only the typed decomposition and nonpromotion proofs.
-- BOM owns its institutional statements; Berger/Sherrington own the audit
-- allegations; 2GB owns its program description; reporters own reporting.
-- No audit data, audio transcript, institutional motive, or covert connection
-- is created by this module.

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Governance.TypedGenealogyEdgeExact as Typed
import DASHI.Core.IntersectionalNonFactorability as INF

data RootRole : Set where
  institutionalAccount : RootRole
  publisherOwnedProgramme : RootRole
  ownershipPrimary : RootRole
  journalistReport : RootRole
  independentCommentary : RootRole
  thirdPartyReportedAudit : RootRole

record SourceRoot : Set where
  constructor source-root
  field
    authorOrInstitution : String
    published : String
    title : String
    locator : String
    role : RootRole
    boundedFinding : String
open SourceRoot public

bomStatement : SourceRoot
bomStatement = source-root
  "Australian Bureau of Meteorology" "2026-10-22"
  "The science and truth of Australia's long-term temperature record"
  "https://www.bom.gov.au/the-science-and-truth-of-australias-long-term-temperature-record"
  institutionalAccount
  "BOM confirms 4 post-1910 duplicated months affecting ACORN-SAT (fewer than 200 daily observations in more than 7 million), all pre-1946 handwritten records later manually digitised; says impact is statistically negligible. Cause under examination, punch-card-era transcription a possibility; disputes fraudulent manipulation."

bomMethods : SourceRoot
bomMethods = source-root
  "Australian Bureau of Meteorology" "2026-10 (ACORN-SAT v2.7)"
  "Long-term temperature record: ACORN-SAT"
  "https://www.bom.gov.au/climate/data/acorn-sat/"
  institutionalAccount
  "Explains paper-to-digital transcriptions, separate original observational records, and trend-homogenisation using station changes, instruments and neighbouring sites."

fordhamProgramme : SourceRoot
fordhamProgramme = source-root
  "Ben Fordham / 2GB" "2026-10-19 AEST"
  "'Dodgy data' - Weather Bureau accused of climate conspiracy"
  "https://www.2gb.com/dodgy-data-weather-bureau-accused-of-climate-conspiracy/"
  publisherOwnedProgramme
  "2GB publishes an accusatory title and describes BOM errors discovered after an outside audit. The programme's full spoken words have not been audited against a transcript here."

fordhamPodcast : SourceRoot
fordhamPodcast = source-root
  "Ben Fordham Live / Apple Podcasts listing" "2026-10-18 21:55 UTC"
  "'Dodgy data' - Weather Bureau accused of climate conspiracy"
  "https://podcasts.apple.com/sg/podcast/dodgy-data-weather-bureau-accused-of-climate-conspiracy/id157670116?i=1000796975224"
  publisherOwnedProgramme
  "Listings establish four-minute episode identity and publication time; they are not independent validation of the underlying audit or the spoken claims."

auditReporting : SourceRoot
auditReporting = source-root
  "Graham Lloyd / The Australian, discussed by Joanne Nova" "2026-10-18"
  "BOM's scientific scandal: The raw data is not raw"
  "https://www.cfact.org/2026/10/18/boms-scientific-scandal-the-raw-data-is-not-raw/"
  thirdPartyReportedAudit
  "Reports Berger/Sherrington audit allegations and archival check of Sydney Observatory August 1867/1907 duplicates; full Berger/Sherrington original audit not acquired, so counts of additional anomalous patterns remain allegations."

taptFirstParty : SourceRoot
taptFirstParty = source-root
  "Tapt Media / Laundy Family Office" "2026-05-01"
  "Tapt Media launches as Australia's premier independent audio powerhouse"
  "https://taptmedia.com.au/tapt-media-launches-as-australias-premier-independent-audio-powerhouse/"
  ownershipPrimary
  "Confirms completion of Laundy Family Office purchase of the 2GB/3AW/4BC/6PR network from Nine and rebranding to Tapt Media."

abcSale : SourceRoot
abcSale = source-root
  "ABC News / Ben Butler" "2026-01-30"
  "Nine Radio sold for cut-price $56m to pub tycoon Arthur Laundy"
  "https://www.abc.net.au/news/2026-01-30/nine-radio-sold-to-arthur-laundy-talk-radio-shrinking-audience/106286352"
  journalistReport
  "Independent reporting of the proposed $56m radio sale and Laundy family connections, not evidence of political command over a presenter."

bondiCoverage : SourceRoot
bondiCoverage = source-root
  "RadioInfo Australia" "2026-08-24"
  "2GB takes home Kennedy Award for coverage of Bondi Beach terror attack"
  "https://radioinfo.com.au/news/2gb-takes-home-kennedy-award-for-coverage-of-bondi-beach-terror-attack/"
  journalistReport
  "Documents Ben Fordham, Mark Levy and Will Bottom's award-winning live 2025 Bondi Beach attack coverage; makes no finding that coverage was inflammatory or centrally coordinated."

kyleCompetition : SourceRoot
kyleCompetition = source-root
  "RadioInfo Australia" "2026-03-17"
  "Triple M goes to 2GB for what's happening at KIIS"
  "https://radioinfo.com.au/news/triple-m-goes-to-2gb-for-whats-happening-at-kiis/"
  journalistReport
  "Documents Sydney breakfast radio commercial rivalry involving Fordham and Kyle Sandilands; rivalry is not coordination."

hansonMention : SourceRoot
hansonMention = source-root
  "Senator Sarah Henderson (participant-published interview)" "2026-10-21"
  "Breakfast with Ben Fordham, 2GB, 21 October 2026"
  "https://sarahhenderson.com.au/breakfast-with-ben-fordham-2gb-21-october-2026/"
  publisherOwnedProgramme
  "Interview transcript contains Fordham's question about Pauline Hanson Please Explain cartoons. A topical mention does not establish Fordham-Hanson organisational affiliation."

-- Additional distinct roots: documented media framing is not a verdict
-- about audience effect, guest accuracy, institutional coordination or intent.
bondiFordhamPoliticalSegment : SourceRoot
bondiFordhamPoliticalSegment = source-root
  "Ben Fordham Live / 2GB podcast listing" "2025-12-18"
  "'We're angry' - PM slammed over response to Bondi terror attack"
  "https://music.amazon.co.uk/podcasts/2686e400-47fa-4f4f-94b3-b95934a496b2/episodes/b7dd042e-cf37-47eb-bfc6-b79cc0dcf598/ben-fordham-live-on-2gb-breakfast---highlights-%E2%80%98we%E2%80%99re-angry%E2%80%99---pm-slammed-over-response-to-bondi-terror-attack%E2%9D%97"
  publisherOwnedProgramme
  "Fordham show published a three-minute post-Bondi segment framed as criticism of the Prime Minister's response. Listing does not establish particular anti-Muslim speech, a complete spoken transcript or central coordination."

fordhamLathamArchive : SourceRoot
fordhamLathamArchive = source-root
  "2GB / Ben Fordham interviewing Mark Latham" "2GB archive (undated in page)"
  "Groups using government funding to spread Islamic radicalisation"
  "https://www.2gb.com/?p=75904"
  publisherOwnedProgramme
  "2GB archived a Mark Latham interview describing a Bankstown poetry performance criticising Pauline Hanson and alleging publicly funded radicalisation. Latham owns the quoted allegations; hosting is not verification of them."

aapBondiHansonFabrication : SourceRoot
aapBondiHansonFabrication = source-root
  "Matthew Elmas / AAP FactCheck" "2025-12-15"
  "Disinformation operation targets Bondi terrorist attack"
  "https://prod-ss.aap.com.au/factcheck/disinformation-operation-targets-bondi-terrorist-attack/"
  journalistReport
  "AAP finds fake post-Bondi Hanson quotes falsely proposing mass Muslim citizenship stripping and identifies a foreign-run Facebook operation. It does not attribute that operation to Hanson, Fordham, Bannon or TPAU."

tpaustFirstParty : SourceRoot
tpaustFirstParty = source-root
  "Turning Point Australia" "website accessed 2026-10-24"
  "About"
  "https://tpaust.com.au/about/"
  ownershipPrimary
  "Organisation's own account describes Joel Jammal's leadership, Nigel Farage event organising and conservative media activity. Self-description is not evidence of any Fordham affiliation."

data DataLayer : Set where
  paperOriginal : DataLayer
  digitisedHistoricalObservation : DataLayer
  adjustedACORNSAT : DataLayer
  nationalTrend : DataLayer

data StatementStatus : Set where
  institutionAcknowledged : StatementStatus
  institutionHypothesised : StatementStatus
  independentlyReported : StatementStatus
  allegationNotReproduced : StatementStatus
  notShown : StatementStatus

record BoundedClaim : Set where
  constructor bounded-claim
  field
    subject : String
    layer : DataLayer
    status : StatementStatus
    root : SourceRoot
    exactScope : String
open BoundedClaim public

confirmedDuplicate : BoundedClaim
confirmedDuplicate = bounded-claim
  "Four post-1910 duplicated months" digitisedHistoricalObservation
  institutionAcknowledged bomStatement
  "BOM confirms fewer than 200 affected daily values in ACORN-SAT input, all historical pre-1946."

possiblePunchCards : BoundedClaim
possiblePunchCards = bounded-claim
  "Punch-card-related transcription" digitisedHistoricalObservation
  institutionHypothesised bomStatement
  "Potential mechanism suggested by BOM, not a forensically established causal account."

trendNegligibleBOMPosition : BoundedClaim
trendNegligibleBOMPosition = bounded-claim
  "Negligible long-term trend impact" nationalTrend
  institutionAcknowledged bomStatement
  "This is BOM's own stated impact analysis, not an independently reproduced result in this module."

sydney1867ReportedError : BoundedClaim
sydney1867ReportedError = bounded-claim
  "Sydney Observatory August 1867/1907 duplication" digitisedHistoricalObservation
  independentlyReported auditReporting
  "An archival cross-check is reported; 1867 lies before ACORN-SAT's 1910 start. Do not include it in the BOM's four post-1910 months."

widerManipulationAllegation : BoundedClaim
widerManipulationAllegation = bounded-claim
  "Deliberate / widespread data manipulation" digitisedHistoricalObservation
  allegationNotReproduced auditReporting
  "Berger/Sherrington assertions and interpretations require the source-complete audit, affected station/date IDs and reproducible comparators."

-- The source-audit has not obtained the original Berger/Sherrington report.
-- This is an acquisition obligation, not evidence the report does not exist.
data OriginalAuditReceiptStatus : Set where
  notAcquired : OriginalAuditReceiptStatus
  exactVersionAcquired : OriginalAuditReceiptStatus

canonicalOriginalAuditStatus : OriginalAuditReceiptStatus
canonicalOriginalAuditStatus = notAcquired

-- Reuse the existing typed genealogy calculus. Every installed edge
-- supports ONLY the named relation, never a hidden command or method transfer.
fordhamTo2GB : Typed.TypedGenealogyEdge
fordhamTo2GB = Typed.typedGenealogyEdge
  "BOM-M1" "Ben Fordham" "2GB"
  Typed.personnelContinuity Typed.primary
  (Typed.sourceReceipt "2GB" "Ben Fordham 2GB programme"
    "2026-10-19" (locator fordhamProgramme)
    "Published programme and identified presenter" ∷ [])
  "Fordham hosts and publishes the programme via 2GB."

radioToTapt : Typed.TypedGenealogyEdge
radioToTapt = Typed.typedGenealogyEdge
  "BOM-M2" "2GB" "Tapt Media / Laundy Family Office"
  Typed.organisationalContinuity Typed.primary
  (Typed.sourceReceipt "Tapt Media / Laundy Family Office"
    "Tapt Media launches" "2026-05-01" (locator taptFirstParty)
    "Direct first-party ownership/brand announcement" ∷ [])
  "Ownership of 2GB transferred from Nine to Laundy/Tapt on 1 May 2026."

fordhamAuditBroadcast : Typed.TypedGenealogyEdge
fordhamAuditBroadcast = Typed.typedGenealogyEdge
  "BOM-M3" "Berger/Sherrington audit allegations (as reported)"
  "2GB Ben Fordham 2026-10-19 segment"
  Typed.audienceAdjacency Typed.primary
  (Typed.sourceReceipt "2GB" "Dodgy data" "2026-10-19"
    (locator fordhamProgramme)
    "2GB programme headline and text identify the allegation being broadcast" ∷ [])
  "A same-topic media amplification edge, not proof of investigation authorship, deliberate falsehood, or secret coordination."

-- Claims about institutional transfer must never be installed as factual
-- genealogy edges solely from narrative similarity or ownership.
data UnresolvedOrganisationalHypothesis : Set where
  fordhamTPUSA : UnresolvedOrganisationalHypothesis
  fordhamTPAU : UnresolvedOrganisationalHypothesis
  fordhamBannon : UnresolvedOrganisationalHypothesis
  fordhamHansonCoordination : UnresolvedOrganisationalHypothesis
  fordhamBondiCovertMobilisation : UnresolvedOrganisationalHypothesis

record NonPromotionBoundary : Set where
  constructor nonpromotion-boundary
  field
    rawDigitisationErrorImpliesDeliberateFraud : Bool
    publishedAccusatoryHeadlineProvesFraud : Bool
    homogenisationIsHistoricalTranscription : Bool
    unverifiedCauseIsEstablishedCause : Bool
    publisherOwnershipProvesEditorialDirection : Bool
    sameRhetoricProvesTPUSAOrBannonControl : Bool
    bondiCoverageProvesInflammatoryContent : Bool
    topicMentionProvesHansonCollaboration : Bool
    radioRivalryProvesKyleCoordination : Bool
    correctionNeedsSameObjectDataComparison : Bool
open NonPromotionBoundary public

canonicalNonPromotionBoundary : NonPromotionBoundary
canonicalNonPromotionBoundary = nonpromotion-boundary
  false false false false false false false false false true

data DuplicateImpliesFraud : Set where
data RhetoricImpliesBannonControl : Set where
data OwnershipImpliesEditorialOrder : Set where
data BondiCoverageImpliesInflammatorySpeech : Set where

duplicateDoesNotProveFraud : DuplicateImpliesFraud → ⊥
duplicateDoesNotProveFraud ()

rhetoricDoesNotProveBannonControl : RhetoricImpliesBannonControl → ⊥
rhetoricDoesNotProveBannonControl ()

ownershipDoesNotProveEditorialOrder : OwnershipImpliesEditorialOrder → ⊥
ownershipDoesNotProveEditorialOrder ()

bondiCoverageDoesNotProveInflammatorySpeech :
  BondiCoverageImpliesInflammatorySpeech → ⊥
bondiCoverageDoesNotProveInflammatorySpeech ()


------------------------------------------------------------------------
-- ORIGINAL-CLAIM DISCRIMINATOR (25 October 2026)
--
-- Source attribution: Graham Readfearn, Guardian 25 Oct 2026, independently
-- interrogates Berger/Sherrington's Palmerville 2004 17 x 31 C allegation.
-- BOM says its historical Palmerville values were recorded to nearest degree.
-- Neither source supplies a verified full audit input deck or original
-- 17-day measurement instrument log in this module.
------------------------------------------------------------------------

readfearnPalmervillePrecisionCheck : SourceRoot
readfearnPalmervillePrecisionCheck = source-root
  "Graham Readfearn / The Guardian" "2026-10-25"
  "The Australian reports 'widespread errors' in BoM temperature data. Where is the evidence for those big claims?"
  "https://www.theguardian.com/environment/2026/oct/25/bom-temperature-record-keeping-under-attack-again"
  journalistReport
  "Readfearn reports BOM's response to a specific audit assertion: 17 successive Palmerville readings of 31 C in 2004 can be influenced by nearest-whole-degree recording precision. The newspaper's reporting and institutional explanation are not an independently reconstructed 2004 station record."

-- Finite model of information erased by rounding. All 17 published days
-- can read 31 C while two hypothetical histories disagree about the first
-- underlying temperature (31.0 C versus 30.6 C in tenths of a degree).
-- A second varied-history endpoint can be 31.4 C. This is not a station
-- reconstruction, random model, probability estimate or proof that 2004
-- measurements were in fact produced by either hypothetical history.

data PalmervilleLatentHistory : Set where
  allDaysExactly310Tenths : PalmervilleLatentHistory
  firstDay306OtherDaysVary : PalmervilleLatentHistory

data PalmervilleSeventeenDayObservedReport : Set where
  seventeenWholeDegree31Reports : PalmervilleSeventeenDayObservedReport

roundedSeventeenDayObservation :
  PalmervilleLatentHistory → PalmervilleSeventeenDayObservedReport
roundedSeventeenDayObservation _ = seventeenWholeDegree31Reports

firstDayTenths : PalmervilleLatentHistory → Nat
firstDayTenths allDaysExactly310Tenths = 310
firstDayTenths firstDay306OtherDaysVary = 306

lastDayTenths : PalmervilleLatentHistory → Nat
lastDayTenths allDaysExactly310Tenths = 310
lastDayTenths firstDay306OtherDaysVary = 314

palmervilleSamePublishedValues :
  roundedSeventeenDayObservation allDaysExactly310Tenths ≡
  roundedSeventeenDayObservation firstDay306OtherDaysVary
palmervilleSamePublishedValues = refl

palmervilleDifferentUnderlyingValue :
  firstDayTenths allDaysExactly310Tenths ≡
  firstDayTenths firstDay306OtherDaysVary → ⊥
palmervilleDifferentUnderlyingValue ()

palmervillePrecisionLossWitness :
  INF.NonFactorabilityWitness roundedSeventeenDayObservation firstDayTenths
palmervillePrecisionLossWitness = INF.nonFactorabilityWitness
  allDaysExactly310Tenths firstDay306OtherDaysVary
  palmervilleSamePublishedValues palmervilleDifferentUnderlyingValue

palmervilleRoundedValuesCannotDetermineUnroundedDayOne :
  INF.FactorsThrough roundedSeventeenDayObservation firstDayTenths → ⊥
palmervilleRoundedValuesCannotDetermineUnroundedDayOne =
  INF.witnessRulesOutEveryFlatFactorisation palmervillePrecisionLossWitness
