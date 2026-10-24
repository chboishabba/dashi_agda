module DASHI.Governance.FriendlyjordiesABCFazalSourceAudit2026Exact where

-- 2026-10-24 bounded update: journalist safety, institutional response,
-- published-media source verification and disputed attributed messages.
-- Source- and claim-locality only; no verdict on contested threat passage.
-- Reuses the existing Friendlyjordies/SensibLaw narrative owners instead of
-- creating a competing global evidence or ontology system.

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.TypedGenealogyEdgeExact as Typed
import DASHI.Governance.FriendlyjordiesNarrativeGovernanceTransportExact as Narrative
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSourceTotalityExact as SourceTotality
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesCompetingNarrativeExact as Comparison

-- Distinct source roots; syndication, quoting and participant accounts are
-- not independently corroborating copies of one originating allegation.
videoRoot : Typed.SourceReceipt
videoRoot = Typed.sourceReceipt
  "Jordan Shanks / friendlyjordies"
  "breaking my silence"
  "2026-10-22; video 39m13s"
  "https://www.youtube.com/watch?v=0Mo_tYIMMnU"
  "Original publisher video is an attributed accusation of institutional failures and a description of the creator's experiences; original video exists but the complete timed spoken transcript is not ingested into this case."

mwmRoot : Typed.SourceReceipt
mwmRoot = Typed.sourceReceipt
  "Joshua Barnett / Michael West Media"
  "Take it to the police: How ABC brushed off FriendlyJordies warnings about reporter"
  "2026-10-23"
  "https://michaelwest.com.au/take-it-to-the-police-how-abc-brushed-off-friendlyjordies-warnings-about-reporter/"
  "Independent dated investigation narrates 2024 warnings, 2025 disputed message publication, ABC response, 2026 findings and 2022 arson, with strict denied/confirmed source distinctions."

abcBoardResponse : Typed.SourceReceipt
abcBoardResponse = Typed.sourceReceipt
  "Australian Broadcasting Corporation"
  "ABC response to Ombudsman review of Cocaine Nation and Meth Highway"
  "2026-09-22"
  "https://www.abc.net.au/about/media-centre/statements-and-responses/abc-response-to-ombudsman-review-of-cocaine-nation/107182808"
  "Institutional response: both programmes failed standards; aspects materially misleading; corrections and removals made; seven Ombudsman recommendations accepted and being implemented."

abcOmbudsmanReporting : Typed.SourceReceipt
abcOmbudsmanReporting = Typed.sourceReceipt
  "ABC News / ABC Ombudsman Fiona Cameron"
  "Four Corners episodes breached ABC editorial standards, ombudsman's investigation finds"
  "2026-09-22"
  "https://www.abc.net.au/news/2026-09-22/abc-mahmood-fazal-four-corners-ombudsman-report/105877266"
  "Reports actual Ombudsman findings: deficient verification and misleading presentation of sources in Cocaine Nation and Meth Highway, breaching accuracy, fair and honest dealing, independence and integrity. NOT a finding that Fazal passed threats."

abc2024Defence : Typed.SourceReceipt
abc2024Defence = Typed.sourceReceipt
  "Four Corners / ABC (reproduced in 2026 Barnett chronology)"
  "ABC and Four Corners public support of Mahmood Fazal"
  "2024-05"
  "https://michaelwest.com.au/take-it-to-the-police-how-abc-brushed-off-friendlyjordies-warnings-about-reporter/"
  "Contemporaneous public expressions of support for reporter are quoted by the later review; original 2024 source revision needed to check exact wording/authorities."

abcJulyRemoval : Typed.SourceReceipt
abcJulyRemoval = Typed.sourceReceipt
  "ABC News Corporate"
  "Four Corners Statement: two removed programs"
  "2026-07-24"
  "https://www.abc.net.au/about/media-centre/statements-and-responses/four-corners-statement/106953658"
  "ABC withdrew Cocaine Nation and Meth Highway, referring questions to Ombudsman; explicitly distinguishes this decision from its May 2026 external-podcast employment termination."

abcAugustRemoval : Typed.SourceReceipt
abcAugustRemoval = Typed.sourceReceipt
  "ABC News Corporate"
  "ABC statement: further anonymous source violations"
  "2026-08-17"
  "https://www.abc.net.au/about/media-centre/statements-and-responses/abc-statement/107045888"
  "ABC removed two more programmes and cut one segment, specifying deficiencies in verification policies; source episode counts should not be double-counted."

lamestreamCountercheck : Typed.SourceReceipt
lamestreamCountercheck = Typed.sourceReceipt
  "Scott Mitchell and Osman Faruqi / Lamestream"
  "Exclusive: These Messages Could Destroy A Prominent ABC Journalist. But Are They Real?"
  "2025-10-31"
  "https://www.lamestream.com.au/exclusive-these-messages-could-destroy-a-prominent-abc-journalist-but-are-they-real/"
  "Outlet reports examining purported leaked message images and detecting inconsistencies in most incendiary excerpts that may indicate manipulation. This is a question/competing forensic account, not a final authentication result."

abcMediaWatchOriginal : Typed.SourceReceipt
abcMediaWatchOriginal = Typed.sourceReceipt
  "ABC Media Watch"
  "Four Cornered"
  "2026-08"
  "https://www.abc.net.au/mediawatch/episodes/four/106962434"
  "Original reporting on anonymised sources, later ABC steps and 2024 complaints; it remains commentary/evidence on distinct episodes."

-- Verified first-party 5-page original (published 22 Sept; signed 20 Aug)
-- inspected page-wise, not inferred from headlines or Michael West reporting.
ombudsmanOriginalExecutiveSummary : Typed.SourceReceipt
ombudsmanOriginalExecutiveSummary = Typed.sourceReceipt
  "Fiona Cameron / ABC Ombudsman"
  "Ombudsman Investigation Report: Four Corners, Cocaine Nation and Meth Highway (executive summary)"
  "signed 2026-08-20; ABC published 2026-09-22"
  "https://live-production.wcms.abc-cdn.net.au/39e8eeeffed7acde9a54d3ccc2f2a6fb"
  "Original five-page executive summary, pages 1-3 containing findings 1-5, seven recommendations, methodology and scope; annexure Board terms of reference July 1. Editorial-standard determinations only, not threat/criminal adjudications."

record ExactEditorialFinding : Set where
  constructor exact-editorial-finding
  field
    findingId : String
    programme : String
    editorialStandard : String
    pageInOriginal : String
    narrowOutcome : String
    root : Typed.SourceReceipt
    decidesThreatOrArson : Bool
open ExactEditorialFinding public

finding1DoublePresentation : ExactEditorialFinding
finding1DoublePresentation = exact-editorial-finding
  "F1" "Cocaine Nation" "accuracy 2.2" "PDF page 1"
  "One person appeared in two significantly different roles/presentations, materially misleading viewers."
  ombudsmanOriginalExecutiveSummary false

finding2JasonVerification : ExactEditorialFinding
finding2JasonVerification = exact-editorial-finding
  "F2" "Cocaine Nation" "accuracy 2.1 and 2.2" "PDF page 1"
  "Insufficient independent checking of source Jason's trafficker status/substantive account, with failure to disclose verification limits."
  ombudsmanOriginalExecutiveSummary false

finding3SweeperApproval : ExactEditorialFinding
finding3SweeperApproval = exact-editorial-finding
  "F3" "Cocaine Nation" "fair and honest dealing 5.9c" "PDF page 2"
  "Disguise and anonymous-source decision for the sweeper was not submitted for required higher editorial approval."
  ombudsmanOriginalExecutiveSummary false

finding4BrendanContext : ExactEditorialFinding
finding4BrendanContext = exact-editorial-finding
  "F4" "Meth Highway" "accuracy 2.2" "PDF page 2"
  "Unverified Brendan identity/cook status and reporter relationship undisclosed to audience; materially misleading framing of risk."
  ombudsmanOriginalExecutiveSummary false

finding5InstitutionalIntegrity : ExactEditorialFinding
finding5InstitutionalIntegrity = exact-editorial-finding
  "F5" "both Four Corners programmes" "independence and integrity 1.1" "PDF page 2"
  "Cumulative breakdown in editorial oversight, upward referral, sources, verification and fact checking significantly misled audiences."
  ombudsmanOriginalExecutiveSummary false

canonicalFiveOmbudsmanFindings : List ExactEditorialFinding
canonicalFiveOmbudsmanFindings =
  finding1DoublePresentation
  ∷ finding2JasonVerification
  ∷ finding3SweeperApproval
  ∷ finding4BrendanContext
  ∷ finding5InstitutionalIntegrity
  ∷ []

data RecommendationState : Set where
  recommended : RecommendationState
  abcReportsCompleted : RecommendationState
  abcReportsInProgress : RecommendationState
  completionNotIndependentlyAudited : RecommendationState

record OmbudsmanRecommendation : Set where
  constructor ombudsman-recommendation
  field
    recommendationId : String
    pageInOriginal : String
    requiredAction : String
    ombudsmanRecommended : Bool
    abcPubliclyAccepted : Bool
    independentlyVerifiedImplementation : Bool
open OmbudsmanRecommendation public

r1RemoveProgrammes : OmbudsmanRecommendation
r1RemoveProgrammes = ombudsman-recommendation "R1" "PDF p2"
  "Remove both Four Corners episodes; already removed before the ombudsman executive summary."
  true true false

r2BroaderInquiry : OmbudsmanRecommendation
r2BroaderInquiry = ombudsman-recommendation "R2" "PDF p2"
  "Investigate both broadcasts more comprehensively, beyond only the Ombudsman's scoped anonymous-source examples."
  true true false

r3PublishCorrection : OmbudsmanRecommendation
r3PublishCorrection = ombudsman-recommendation "R3" "PDF p2"
  "Publish visible Corrections and Clarifications acknowledging material misrepresentation."
  true true false

r4NamedAnonymityApprover : OmbudsmanRecommendation
r4NamedAnonymityApprover = ombudsman-recommendation "R4" "PDF p2"
  "Amend standard 5.9 anonymity guidance to identify responsible senior officer, required source verification and audience context."
  true true false

r5LegalVersusEditorialRisk : OmbudsmanRecommendation
r5LegalVersusEditorialRisk = ombudsman-recommendation "R5" "PDF p2"
  "Train team to balance legal/source-protection risk with continued factual verification and editorial accountability."
  true true false

r6FactcheckAndUpwardReferral : OmbudsmanRecommendation
r6FactcheckAndUpwardReferral = ombudsman-recommendation "R6" "PDF p3"
  "Set clear fact-checking and higher editorial escalation expectations."
  true true false

r7JuniorTeamSupport : OmbudsmanRecommendation
r7JuniorTeamSupport = ombudsman-recommendation "R7" "PDF p3"
  "Ensure management support for less experienced reporters on high-risk investigations."
  true true false

canonicalSevenOmbudsmanRecommendations : List OmbudsmanRecommendation
canonicalSevenOmbudsmanRecommendations =
  r1RemoveProgrammes
  ∷ r2BroaderInquiry
  ∷ r3PublishCorrection
  ∷ r4NamedAnonymityApprover
  ∷ r5LegalVersusEditorialRisk
  ∷ r6FactcheckAndUpwardReferral
  ∷ r7JuniorTeamSupport
  ∷ []

-- ABC acceptance and its stated implementation progress cannot prove
-- that all seven recommendations were independently checked and delivered.
data InstitutionalAcceptanceImpliesAuditedCompletion : Set where
institutionalAcceptanceDoesNotPayCompletion :
  InstitutionalAcceptanceImpliesAuditedCompletion → ⊥
institutionalAcceptanceDoesNotPayCompletion ()

data CaseType : Set where
  institutionalPublicResponse : CaseType
  allegedWitnessedWarning : CaseType
  disputedDigitalMessage : CaseType
  publishedCorrection : CaseType
  independentEditorialFinding : CaseType
  verifiedCriminalDisposition : CaseType
  unresolvedCoordinatingActor : CaseType

data SourceDisposition : Set where
  participantAttributed : SourceDisposition
  contemporaneousStatement : SourceDisposition
  reportedWithDenial : SourceDisposition
  independentlyAdjudicated : SourceDisposition
  originalDocumentNotAcquired : SourceDisposition

record MediaCaseClaim : Set where
  constructor media-case-claim
  field
    question : String
    kind : CaseType
    disposition : SourceDisposition
    source : Typed.SourceReceipt
    limit : String
    provesThreatCriminally : Bool
    provesArsonAuthorship : Bool
open MediaCaseClaim public

warningReported : MediaCaseClaim
warningReported = media-case-claim
  "January 2024 warning allegedly delivered via Fazal to Kristo Langker"
  allegedWitnessedWarning reportedWithDenial mwmRoot
  "Based on participant/police statement as reported; Fazal denies passing threats, and no criminal verdict is installed." false false

messagesDisputed : MediaCaseClaim
messagesDisputed = media-case-claim
  "2025 alleged message screenshots naming Shanks"
  disputedDigitalMessage reportedWithDenial lamestreamCountercheck
  "The most incriminating extracts have contested authenticity; exact original exports, device chain and forensic authentication not acquired." false false

abcEarlyPublicDefence : MediaCaseClaim
abcEarlyPublicDefence = media-case-claim
  "2024 ABC public defence and direction to police"
  institutionalPublicResponse contemporaneousStatement abc2024Defence
  "Existence of public response documented through reporting, but internal ABC investigation/no investigation not conclusively reconstructed from internal decision records." false false

abcOmbudsmansDetermination : MediaCaseClaim
abcOmbudsmansDetermination = media-case-claim
  "Accuracy/source-anonymity failures in Cocaine Nation and Meth Highway"
  independentEditorialFinding independentlyAdjudicated abcOmbudsmanReporting
  "Independent ABC Ombudsman editorial review finds deficiencies in two specific programmes; it did NOT adjudicate the 2024 alleged threats or arson mastermind." false false

abcProgramsRemoved : MediaCaseClaim
abcProgramsRemoved = media-case-claim
  "ABC 2026 programme withdrawal/correction"
  publishedCorrection contemporaneousStatement abcBoardResponse
  "ABC accepts source-verification failure and removes/corrects programmes; it also says May employment termination was based on a separate external-work inquiry." false false

data CaseStage : Set where
  firebombing2022 : CaseStage
  reportedThreatWarning2024 : CaseStage
  abcs2024PublicResponse : CaseStage
  podcastAndDisputedMessages2025 : CaseStage
  reporterTerminatedMay2026 : CaseStage
  abcContentWithdrawalsJulyAugust2026 : CaseStage
  ombudsmanFindingsSeptember2026 : CaseStage
  shanksVideoOctober2026 : CaseStage
  michaelWestOctober2026 : CaseStage

chronologicalStages : List CaseStage
chronologicalStages =
  firebombing2022
  ∷ reportedThreatWarning2024
  ∷ abcs2024PublicResponse
  ∷ podcastAndDisputedMessages2025
  ∷ reporterTerminatedMay2026
  ∷ abcContentWithdrawalsJulyAugust2026
  ∷ ombudsmanFindingsSeptember2026
  ∷ shanksVideoOctober2026
  ∷ michaelWestOctober2026
  ∷ []

-- Other events at Bondi are strictly different:
-- 2022 home arson is NOT 2024 Bondi Junction or the December 2025
-- Bondi Beach attack used in the Hanson/Herzog mobilisation lanes.
data BondiEventIdentity : Set where
  shanksHomeArsonNov2022 : BondiEventIdentity
  bondiJunctionAttackApr2024 : BondiEventIdentity
  bondiBeachAttackDec2025 : BondiEventIdentity

record SafetyAndReportingBoundary : Set where
  constructor safety-reporting-boundary
  field
    ombudsmanEditorialBreachProvesThreat : Bool
    authentic2024WarningProvesReporterCriminalLiability : Bool
    disputed2025ScreenshotsAreAuthenticated : Bool
    arsonPerpetratorConvictionIdentifiesMastermind : Bool
    abc2026CorrectionDisprovesAllEarlierReporting : Bool
    failureToInvestigateAsAllegedEqualsProvedCoverup : Bool
    institutionalReviewCanTestInternalEscalation : Bool
    survivorWitnessMustKeepOriginalAttribution : Bool
open SafetyAndReportingBoundary public

canonicalSafetyAndReportingBoundary : SafetyAndReportingBoundary
canonicalSafetyAndReportingBoundary =
  safety-reporting-boundary false false false false false false true true

data EditorialBreachProvesThreat : Set where
data ArsonConvictionProvesMastermind : Set where
data DisputedMessagesBecomeAuthenticByPublication : Set where
data ABCResponseProvesConspiracy : Set where

noThreatPromotion : EditorialBreachProvesThreat → ⊥
noThreatPromotion ()
noMastermindPromotion : ArsonConvictionProvesMastermind → ⊥
noMastermindPromotion ()
noScreenGrabTruthPromotion : DisputedMessagesBecomeAuthenticByPublication → ⊥
noScreenGrabTruthPromotion ()
noCoverupPromotion : ABCResponseProvesConspiracy → ⊥
noCoverupPromotion ()

-- Existing canonical prior art is intentionally imported for a compile-time
-- relationship and semantic/proposition scope, not used to decide facts.
narrativeOwner : Narrative.GovernanceWitness
narrativeOwner = Narrative.friendlyjordiesGovernanceWitness

sourceTotalityRevision : String
sourceTotalityRevision = Comparison.sensibLawRevision

data CaseOwnerReuse : Set where
  originalFJPublicClaimTrace : CaseOwnerReuse
  sourceTotalityNoOrphans : CaseOwnerReuse
  competingAccountsNoTruthCollapse : CaseOwnerReuse
  existingInstitutionalReviewLane : CaseOwnerReuse

canonicalCaseOwnerReuse : List CaseOwnerReuse
canonicalCaseOwnerReuse =
  originalFJPublicClaimTrace
  ∷ sourceTotalityNoOrphans
  ∷ competingAccountsNoTruthCollapse
  ∷ existingInstitutionalReviewLane
  ∷ []
