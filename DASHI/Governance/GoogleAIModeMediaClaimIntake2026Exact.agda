module DASHI.Governance.GoogleAIModeMediaClaimIntake2026Exact where

-- User-supplied Google AI Mode conversation: a lead-generation text,
-- not an independently corroborating news report. Its factual claims
-- must be joined to independent dated roots. Research intake 25 Oct 2026.
-- SHA256 of exact uploaded bytes (not the share URL's inaccessible bytes):
-- 80b27d5b866a0a906142a6c66f3e090ad39342ecbe4173f088ef48ea61adbfcc
-- 561 lines; 60685 bytes. Preserve source roots, denials, claim ownership.
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Governance.TypedGenealogyEdgeExact as Typed
import DASHI.Governance.AustralianPoliticalRadioInfluence2026Exact as A

googleConversationRoot : Typed.SourceReceipt
googleConversationRoot = Typed.sourceReceipt
  "Google AI Mode assistant output supplied by the user"
  "Australian broadcast/media/mining/Bannon/Epstein discussion; original share URL"
  "timestamps in user export 22:37-22:50 AEST; uploaded 2026-10-25"
  "https://share.google/aimode/Ux4UtsL535FOH9STw"
  "Original share endpoint blocked; user-uploaded 561-line text acquired and SHA256 checked. Secondary generated claims are NOT separate journalistic or archival evidence."

-- The 2024 event provides an actual, date-bounded co-attendance link,
-- NOT any instruction, contract or financial relationship between guests.
rinehartBannonDevineEvent : A.RelationshipReceipt
rinehartBannonDevineEvent = A.relationship-receipt
  "Gina Rinehart and Steve Bannon" "Miranda Devine Manhattan book launch"
  A.conferenceCoAttendance A.journalistCorroboration
  "Daanyal Saeed, Crikey, 6 Nov 2024"
  "https://www.crikey.com.au/2024/11/06/australian-conservatives-normal-us-election/"
  "Crikey reports both Rinehart and Bannon attended Devine's Manhattan book launch. Co-attendance supports proximity, NOT sponsorship or political direction."
  false false false

-- Note: Saturday Paper says 'spotted chatting', not strategic meetings.
advanceSheahanBannonConversation : A.RelationshipReceipt
advanceSheahanBannonConversation = A.relationship-receipt
  "Matthew Sheahan / Advance" "Steve Bannon"
  A.reportedMeeting A.journalistCorroboration
  "Mike Seccombe, The Saturday Paper, 7 Feb 2026"
  "https://www.thesaturdaypaper.com.au/news/politics/2026/02/07/did-steve-bannon-stop-labor-winning-2019"
  "Article says Sheahan had been spotted chatting with Bannon in Washington; supplies no verified meeting agenda, strategic instruction, formal contract or causal campaign join."
  false false false

rinehartMcWilliamSecuredMediaStake : A.RelationshipReceipt
rinehartMcWilliamSecuredMediaStake = A.relationship-receipt
  "Gina Rinehart / Hancock-related financing" "Bruce McWilliam Southern Cross Media shares"
  A.securedStakeFinancing A.journalistCorroboration
  "Guardian business 27 May 2026; ASX security deed reported"
  "https://www.theguardian.com/business/2026/may/27/gina-rinehart-pays-for-bruce-mcwilliam-purchase-southern-cross-media"
  "About AUD26m financing for near-10% stake in Seven/Hit/Triple M parent, with relevant interest and contingent security/voting rights. Not direct outright ownership, and not editorial control."
  false false false

rinehartStefanovicPodcastFundingClaim : A.RelationshipReceipt
rinehartStefanovicPodcastFundingClaim = A.relationship-receipt
  "The Australian / The Front reporting" "Rinehart financing of Stefanovic podcast"
  A.reportedUnverifiedFunding A.journalistCorroboration
  "The Australian, The Front, 29 Jun 2026 AEST"
  "https://podcasts.apple.com/za/podcast/did-the-ben-roberts-smith-drama-end-karl-stefanovics-career/id1614339406?i=1000774589371"
  "Publisher says Rinehart 'appears' to have bankrolled the podcast; contract, amount, funding route and editorial conditions not acquired. Repeating publisher wording does NOT verify completed funding."
  false false false

stefanovicRobinsonPublication : A.RelationshipReceipt
stefanovicRobinsonPublication = A.relationship-receipt
  "The Karl Stefanovic Show" "Tommy Robinson interview"
  A.editorialPublication A.journalistCorroboration
  "ABC 24-26 June 2026"
  "https://www.abc.net.au/news/2026-06-24/karl-stefanovic-tommy-robinson-podcast-interview-taken-offline/106834832"
  "Podcast interview published then removed from Stefanovic platforms. Nine confirmed his departure 26 June. A platforming act is not evidence of Bannon oversight."
  false false false

hansonRepublishedRobinson : A.RelationshipReceipt
hansonRepublishedRobinson = A.relationship-receipt
  "Pauline Hanson official video channel" "Stefanovic-Robinson interview"
  A.mediaRedistribution A.journalistCorroboration
  "ABC/Guardian reporting 24-25 June 2026"
  "https://www.abc.net.au/news/2026-06-24/karl-stefanovic-tommy-robinson-podcast-interview-taken-offline/106834832"
  "Hanson republished a recording. Platform redistribution is observable, but publisher permission, a business agreement or command chain was not established."
  false false false

mandelsonXstrataEpsteinTaxEmail : A.RelationshipReceipt
mandelsonXstrataEpsteinTaxEmail = A.relationship-receipt
  "Peter Mandelson" "Jeffrey Epstein / forwarded Xstrata mining-tax correspondence"
  A.publishedCorrespondence A.journalistCorroboration
  "Ben Butler, ABC, 2 Feb 2026, reporting on released DOJ emails from June 2010"
  "https://www.abc.net.au/news/2026-02-02/peter-mandelson-on-rudds-mining-super-profits-tax-epstein-files/106295236"
  "A concrete Australian resource-tax information path: Mandelson emailed Epstein campaign analysis enclosing material from Xstrata chief Mick Davis. Does NOT prove Epstein directed Australia's mining lobby or Rudd's removal."
  false false false

ruddMentionNotContact : A.RelationshipReceipt
ruddMentionNotContact = A.relationship-receipt
  "Third-party Epstein correspondence" "Kevin Rudd"
  A.publishedCorrespondence A.journalistCorroboration
  "ABC, 31 Jan 2026 DOJ correspondence audit"
  "https://www.abc.net.au/news/2026-01-31/kevin-rudd-refred-to-in-latest-epstein-files-dump/106290858"
  "Emails and calendar refer to proposed invitations/meetings. ABC saw no direct correspondence between Rudd and Epstein. Appearance in documents is NOT attendance or wrongdoing."
  false false false

ruddDeniedEpsteinMeeting : A.RelationshipReceipt
ruddDeniedEpsteinMeeting = A.relationship-receipt
  "Kevin Rudd's office" "meeting/correspondence with Jeffrey Epstein"
  A.disputedAuthorshipClaim A.namedActorDenial
  "ABC quoting Rudd's office, 31 Jan 2026"
  "https://www.abc.net.au/news/2026-01-31/kevin-rudd-refred-to-in-latest-epstein-files-dump/106290858"
  "Office denied any introduction or direct contact, while confirming a dinner at third party Jagland's residence. This is a response to attempted-introduction evidence, not a criminal exoneration judgement."
  false false false

jonesGillardRecordedRemark : A.RelationshipReceipt
jonesGillardRecordedRemark = A.relationship-receipt
  "Alan Jones at Sydney University Liberal Club dinner" "Julia Gillard / her late father"
  A.editorialPublication A.journalistCorroboration
  "ABC, 30 Sep 2012, contemporaneous recording and apology"
  "https://www.abc.net.au/news/2012-09-30/jones-says-pms-dad-27died-of-shame27/4287770"
  "The offensive recorded comment, Jones's subsequent apology and advertiser backlash are independently reported. This 2012 source predates the 2019 Bannon-Palmer claims; similar rhetoric is not proof of shared command."
  false false false

rinehartJonesArchiveScrub : A.RelationshipReceipt
rinehartJonesArchiveScrub = A.relationship-receipt
  "Hancock Prospecting and S Kidman websites" "Historical Alan Jones references"
  A.editorialPublication A.journalistCorroboration
  "SMH/Mediaweek reporting Nov 2024"
  "https://www.mediaweek.com.au/media-roundup-alan-jones-supporters-waiver-could-hadley-give-evidence-star-reporters-creepy-jones-interview-guardian-investigates-kyle-and-jackie-o-vulgar-content/"
  "Archived corporate Jones mentions reportedly removed after arrest; motive, timing precision and operational direction not independently established."
  false false false

-- Canonical receipt already resides in another PR and is not copied:
-- PR #1131, BannonFaragePalmerAutomatedInfluenceReceiptsExact,
-- DOJ EFTA01615861, Bannon's claim / Palmer's denial.
canonicalBannonPalmerOwner : A.RelationshipReceipt
canonicalBannonPalmerOwner = A.relationship-receipt
  "PR #1131" "Bannon-Farage-Palmer receipt"
  A.publishedCorrespondence A.institutionRecord
  "Cross-branch canonical ownership"
  "https://github.com/chboishabba/dashi_agda/pull/1131"
  "Reference original DOJ evidence and reply in the canonical owner; this does not promote disputed direction or suggest Palmer met Epstein."
  false false false

-- Generated share answers can propose leads, not independently verify them.
-- A chain of event, funding or document mentions does not manufacture
-- personal acquaintance, editorial instruction, or criminal participation.
data GeneratedAnswerIsIndependentSource : Set where
data SharedEventProvesDirection : Set where
data EpsteinDocumentMentionProvesMeeting : Set where
data SecuredMediaFinanceProvesEditorialOrders : Set where
data ReportedPodcastBackerIsAuditedCapital : Set where

noSyntheticCorroboration : GeneratedAnswerIsIndependentSource → ⊥
noSyntheticCorroboration ()
noCoattendanceDirection : SharedEventProvesDirection → ⊥
noCoattendanceDirection ()
noMentionMeeting : EpsteinDocumentMentionProvesMeeting → ⊥
noMentionMeeting ()
noFinanceCommand : SecuredMediaFinanceProvesEditorialOrders → ⊥
noFinanceCommand ()
noRumourToEquity : ReportedPodcastBackerIsAuditedCapital → ⊥
noRumourToEquity ()
