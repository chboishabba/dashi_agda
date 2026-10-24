module DASHI.Cognition.ZorroPetroglyphSourceCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.ReleasedArtifactProvenanceBidiExact as Released
import DASHI.Core.ProvenanceClosureIndependenceExact as Lineage

------------------------------------------------------------------------
-- ZORRO RANCH PETROGLYPHS -- SOURCE ROLE / ROOT / CLAIM DISCIPLINE
--
-- This is a claim-typing and source-genealogy model, NOT a finding
-- of criminal liability, actual rock-cutting, a supernatural mechanism
-- or a source-verification receipt for unopened original DOJ PDF pages.
--
-- Source anchors:
-- DOJ Dataset 9 EFTA00578213, 4 April 2001, ranch task list
-- DOJ Dataset 9 EFTA00990932, 7 June 2014, outgoing question
-- DOJ Dataset 9 EFTA00694234, 7 June 2014, reply quoting same question
-- James Mahu, WingMakers Collected Works 1 (2013), copyright page:
-- Ancient Arrow Project novel and Neruda interviews designated fiction
-- NMDOJ 19 Feb / 9 Mar / 5 Aug / 21 Oct 2026 institutional records
-- Clara Bates (2026) and attributed Pueblo council response
------------------------------------------------------------------------

data SourceObject : Set where
  ranchTasks2001 : SourceObject
  myhrvoldOutgoing2014 : SourceObject
  myhrvoldReply2014 : SourceObject
  wingMakersAuthorEdition2013 : SourceObject
  batesReporting2026 : SourceObject
  puebloCouncilStatement2026 : SourceObject
  newMexicoFebStatement : SourceObject
  newMexicoMarSearchStatement : SourceObject
  newMexicoAugRecordsSuit : SourceObject
  newMexicoOctCivilSuit : SourceObject
  instagramReel2026 : SourceObject

data Root : Set where
  ranchAdministration : Root
  june2014Correspondence : Root
  mahuAuthorEdition : Root
  batesJournalism : Root
  puebloCouncil : Root
  newMexicoJustice : Root
  reelSpeaker : Root

sourceRoot : SourceObject → Root
sourceRoot ranchTasks2001 = ranchAdministration
sourceRoot myhrvoldOutgoing2014 = june2014Correspondence
sourceRoot myhrvoldReply2014 = june2014Correspondence
sourceRoot wingMakersAuthorEdition2013 = mahuAuthorEdition
sourceRoot batesReporting2026 = batesJournalism
sourceRoot puebloCouncilStatement2026 = puebloCouncil
sourceRoot newMexicoFebStatement = newMexicoJustice
sourceRoot newMexicoMarSearchStatement = newMexicoJustice
sourceRoot newMexicoAugRecordsSuit = newMexicoJustice
sourceRoot newMexicoOctCivilSuit = newMexicoJustice
sourceRoot instagramReel2026 = reelSpeaker

same2014ThreadRoot :
  sourceRoot myhrvoldOutgoing2014 ≡
  sourceRoot myhrvoldReply2014
same2014ThreadRoot = refl

newMexicoActionsShareInstitutionalRoot :
  sourceRoot newMexicoFebStatement ≡
  sourceRoot newMexicoOctCivilSuit
newMexicoActionsShareInstitutionalRoot = refl

------------------------------------------------------------------------
-- An occurrence in released records is not proof of every surrounding
-- interpretation. Distinct claim constructors prohibit silent identity.
------------------------------------------------------------------------

data Claim : Set where
  taskListReportsOneRockMoved : Claim
  outgoingQuestionAboutCuttingPolishing : Claim
  recipientPromisesFurtherEmail : Claim
  physicalPolishingCompleted : Claim
  provenanceAndContextRecovered : Claim
  originalAuthorDeclaresFiction : Claim
  wingMakersInstitutionalOperation : Claim
  controlledPastDirectedSignal : Claim
  stateAnnouncesSearch : Claim
  stateFilesCivilComplaint : Claim
  complaintAllegationsAdjudicated : Claim

reportedMovementNotPolishing :
  taskListReportsOneRockMoved ≡ physicalPolishingCompleted → ⊥
reportedMovementNotPolishing ()

questionNotExecution :
  outgoingQuestionAboutCuttingPolishing ≡ physicalPolishingCompleted → ⊥
questionNotExecution ()

fictionNotIntelligenceOperation :
  originalAuthorDeclaresFiction ≡ wingMakersInstitutionalOperation → ⊥
fictionNotIntelligenceOperation ()

complaintNotAdjudication :
  stateFilesCivilComplaint ≡ complaintAllegationsAdjudicated → ⊥
complaintNotAdjudication ()

data SourceRole : Set where
  ranchTaskRecord : SourceRole
  outgoingCorrespondence : SourceRole
  replyCorrespondence : SourceRole
  authorEditionStatement : SourceRole
  originalJournalism : SourceRole
  quotedCommunityStatement : SourceRole
  officialAgencyAnnouncement : SourceRole
  complaintAllegation : SourceRole
  attributedReelAssertion : SourceRole

data ClaimStanding : Set where
  documentedAsRecorded : ClaimStanding
  reportedBySource : ClaimStanding
  originalAuthorStatement : ClaimStanding
  filingEstablishedAllegationsUnadjudicated : ClaimStanding
  hypothesisNoSameObjectEvidence : ClaimStanding

record SourceClaimReceipt : Set where
  constructor receipt
  field
    source : SourceObject
    role : SourceRole
    claim : Claim
    standing : ClaimStanding
    locator : String
    ceiling : String

rockMovementReceipt : SourceClaimReceipt
rockMovementReceipt = receipt ranchTasks2001 ranchTaskRecord
  taskListReportsOneRockMoved documentedAsRecorded
  "EFTA00578213, first ranch task-list page, 4 April 2001"
  "Ranch list reports one rock placed in former dog yard; exact original PDF image uninspected here."

cuttingInquiryReceipt : SourceClaimReceipt
cuttingInquiryReceipt = receipt myhrvoldOutgoing2014 outgoingCorrespondence
  outgoingQuestionAboutCuttingPolishing documentedAsRecorded
  "EFTA00990932, 7 June 2014"
  "Question about how to cut/polish boulders; no work-order or execution inferred."

replyReceipt : SourceClaimReceipt
replyReceipt = receipt myhrvoldReply2014 replyCorrespondence
  recipientPromisesFurtherEmail documentedAsRecorded
  "EFTA00694234, 7 June 2014"
  "Same question quoted, one correspondence root; reply is not completion proof."

fictionReceipt : SourceClaimReceipt
fictionReceipt = receipt wingMakersAuthorEdition2013 authorEditionStatement
  originalAuthorDeclaresFiction originalAuthorStatement
  "James Mahu, Collected Works of WingMakers vol 1, 2013, copyright page"
  "Own-work fiction designation, not proof of any factual Ancient Arrow operation."

stateCivilComplaintReceipt : SourceClaimReceipt
stateCivilComplaintReceipt = receipt newMexicoOctCivilSuit complaintAllegation
  stateFilesCivilComplaint filingEstablishedAllegationsUnadjudicated
  "NMDOJ 21 October 2026, Indyke/Kahn civil complaint announcement"
  "Filing existence established; contested claims and individual liability not adjudicated."
