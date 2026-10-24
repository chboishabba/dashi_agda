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
