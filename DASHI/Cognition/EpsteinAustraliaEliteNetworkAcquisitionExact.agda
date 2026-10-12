module DASHI.Cognition.EpsteinAustraliaEliteNetworkAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- AUSTRALIAN EPSTEIN / MAXWELL ACQUISITION OWNER
--
-- Public-source nomination is not treated as proof of a direct relationship.
-- This owner distinguishes direct correspondence/social contact, third-party
-- mention, disputed historical reporting, and investigative/evidence-recovery
-- activity in Australia.
------------------------------------------------------------------------

data AustraliaEdgeKind : Set where
  katherineKeatingDirectRelationship : AustraliaEdgeKind
  kevinRuddAttemptedIntroduction : AustraliaEdgeKind
  andrewForrestThirdPartyMention : AustraliaEdgeKind
  clivePalmerBannonClaim : AustraliaEdgeKind
  foxPacker1995CruiseReport : AustraliaEdgeKind
  fbiAFP2011EvidenceRecovery : AustraliaEdgeKind
  ginaRinehartNoPaidDirectEdge : AustraliaEdgeKind

record AustraliaReceipt : Set where
  constructor australia-receipt
  field
    edgeKind : AustraliaEdgeKind
    sourceDescription : String
    directRelationshipEstablished : Bool
    sourceConflictOrDenial : Bool
    wrongdoingEstablishedByThisReceipt : Bool
    needsPrimaryResolution : Bool
open AustraliaReceipt public

katherineKeatingReceipt : AustraliaReceipt
katherineKeatingReceipt = australia-receipt
  katherineKeatingDirectRelationship
  "ABC 2026 reporting on DOJ-released emails describes a direct social/business-network relationship between Katherine Keating and Epstein spanning 2010-2013, including dinners, correspondence, introductions and career/business-networking context."
  true false false true

ruddReceipt : AustraliaReceipt
ruddReceipt = australia-receipt
  kevinRuddAttemptedIntroduction
  "ABC 2026: Epstein correspondence records attempts or plans to connect with Kevin Rudd, while Rudd's office says he never met or corresponded with Epstein and no completed meeting is established."
  false true false true

forrestReceipt : AustraliaReceipt
forrestReceipt = australia-receipt
  andrewForrestThirdPartyMention
  "ABC/Australian 2026: Andrew Forrest appears in third-party correspondence; his representatives say he never met Epstein. Mention is retained as nomination only."
  false true false true

palmerReceipt : AustraliaReceipt
palmerReceipt = australia-receipt
  clivePalmerBannonClaim
  "ABC 2026: Steve Bannon told Epstein that he had influenced Clive Palmer's political advertising; Palmer denied Bannon influenced him and no Palmer-Epstein contact is established."
  false true false true

foxPackerReceipt : AustraliaReceipt
foxPackerReceipt = australia-receipt
  foxPacker1995CruiseReport
  "A 1995 Sydney newspaper report described Epstein and Ghislaine Maxwell as guests of honour on a harbour cruise associated with Lindsay Fox and listed James Packer among invitees/guests; Fox later denied meeting them and said he was in Hawaii. Keep the event source-conflicted pending primary archival resolution."
  false true false true

fbiAFPReceipt : AustraliaReceipt
fbiAFPReceipt = australia-receipt
  fbiAFP2011EvidenceRecovery
  "Giuffre v Maxwell court records and 2026 Guardian reporting establish that FBI agents met Giuffre in Sydney in 2011, with Australian assistance, and took original photographs into evidence including the Andrew-Maxwell-Giuffre image."
  true false false false

ginaRinehartReceipt : AustraliaReceipt
ginaRinehartReceipt = australia-receipt
  ginaRinehartNoPaidDirectEdge
  "Current public-source sweep did not establish a direct Gina Rinehart-Epstein relationship. Absence from this receipt set is not proof of universal non-contact."
  false false false true

------------------------------------------------------------------------
-- Attribution firewalls.
------------------------------------------------------------------------

data MentionImpliesRelationship : Set where
data PlannedMeetingImpliesCompletedMeeting : Set where
data ThirdPartyClaimImpliesDirectContact : Set where
data DisputedNewspaperReportImpliesEstablishedEvent : Set where
data EvidenceRecoveryJurisdictionImpliesLocalComplicity : Set where
data NoCurrentReceiptImpliesNeverConnected : Set where

mentionDoesNotCreateRelationship : MentionImpliesRelationship → ⊥
mentionDoesNotCreateRelationship ()

plannedMeetingDoesNotCreateCompletedMeeting : PlannedMeetingImpliesCompletedMeeting → ⊥
plannedMeetingDoesNotCreateCompletedMeeting ()

thirdPartyClaimDoesNotCreateDirectContact : ThirdPartyClaimImpliesDirectContact → ⊥
thirdPartyClaimDoesNotCreateDirectContact ()

disputedReportDoesNotCreateEstablishedEvent : DisputedNewspaperReportImpliesEstablishedEvent → ⊥
disputedReportDoesNotCreateEstablishedEvent ()

evidenceRecoveryDoesNotCreateLocalComplicity : EvidenceRecoveryJurisdictionImpliesLocalComplicity → ⊥
evidenceRecoveryDoesNotCreateLocalComplicity ()

noReceiptDoesNotProveNeverConnected : NoCurrentReceiptImpliesNeverConnected → ⊥
noReceiptDoesNotProveNeverConnected ()

record AustraliaAcquisitionBoundary : Set where
  constructor australia-acquisition-boundary
  field
    katherineKeatingDirectRelationshipPaid : Bool
    australiaEvidenceRecoveryRolePaid : Bool
    ruddDirectRelationshipPaid : Bool
    forrestDirectRelationshipPaid : Bool
    palmerDirectRelationshipPaid : Bool
    foxPackerCruiseUncontested : Bool
    ginaRinehartDirectRelationshipPaid : Bool
open AustraliaAcquisitionBoundary public

canonicalAustraliaAcquisitionBoundary : AustraliaAcquisitionBoundary
canonicalAustraliaAcquisitionBoundary = australia-acquisition-boundary
  true true false false false false false
