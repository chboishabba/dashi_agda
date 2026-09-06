module DASHI.Law.AustraliaMilitaryMarathonSecuritySourceReceiptsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source receipts for two contemporary military/security contexts.
------------------------------------------------------------------------

data ContemporarySourceRole : Set where
  primeMinisterOfficialStatement
  parliamentaryRecord
  abcReport
  investigativeJournalism
  civilSocietyLegalAdvocacy
  eventOrganiserOrCommunityReport
  dashiCorrection : ContemporarySourceRole

data ContemporaryProposition : Set where
  threeAustraliansAboardUSSubmarine
  iranianVesselWasFrigateWarship
  australianPersonnelParticipatedInAttack
  australiansOrderedToBunks
  israeliMilitaryBackgroundDelegationAtSydneyMarathon
  sixServingIDFRunnersPoliceProtectedReport
  dedicatedRunningPoliceProtectionOfficiallyConfirmed
  generalMarathonHighVisibilityPoliceOperation : ContemporaryProposition

record ContemporarySourceReceipt : Set where
  constructor contemporarySourceReceipt
  field
    proposition : ContemporaryProposition
    role : ContemporarySourceRole
    authorOrInstitution : String
    title : String
    stableIdentifier : String
    boundedDescription : String
    promotesWorldTruth : Bool

open ContemporarySourceReceipt public

threeAustraliansReceipt : ContemporarySourceReceipt
threeAustraliansReceipt = contemporarySourceReceipt
  threeAustraliansAboardUSSubmarine primeMinisterOfficialStatement
  "Anthony Albanese, Prime Minister of Australia"
  "Television interview - Sky Newsday"
  "6 March 2026; https://www.pm.gov.au/media/television-interview-sky-newsday-0"
  "Prime Minister confirmed three Australian personnel were aboard the US submarine that sank the Iranian vessel"
  true

warshipCorrectionReceipt : ContemporarySourceReceipt
warshipCorrectionReceipt = contemporarySourceReceipt
  iranianVesselWasFrigateWarship abcReport
  "Tom Lowrey and Stephen Dziedzic, ABC News"
  "Anthony Albanese confirms Australian navy personnel on US submarine that sank Iranian vessel"
  "ABC News, 6 March 2026"
  "The sunk vessel was IRIS Dena, an Iranian frigate/warship; current reliable sources do not support describing this incident as the sinking of a civilian ship"
  true

nonParticipationGovernmentReceipt : ContemporarySourceReceipt
nonParticipationGovernmentReceipt = contemporarySourceReceipt
  australianPersonnelParticipatedInAttack primeMinisterOfficialStatement
  "Anthony Albanese, Prime Minister of Australia"
  "Television interview - Sky Newsday"
  "6 March 2026"
  "Prime Minister stated that no Australian personnel participated in offensive action; this is an executive assertion about participation, not independently reconstructed crew-action evidence"
  false

notOrderedToBunksReceipt : ContemporarySourceReceipt
notOrderedToBunksReceipt = contemporarySourceReceipt
  australiansOrderedToBunks primeMinisterOfficialStatement
  "Vice Admiral Mark Hammond, Chief of Navy, Defence Ministers press conference"
  "Press Conference, Sydney"
  "21 March 2026"
  "Chief of Navy answered 'No' when asked whether Australian submariners were ordered to their bunks; he said they performed duties in accordance with US-Australia arrangements while not engaged in offensive operations"
  false

acijMarathonReceipt : ContemporarySourceReceipt
acijMarathonReceipt = contemporarySourceReceipt
  israeliMilitaryBackgroundDelegationAtSydneyMarathon civilSocietyLegalAdvocacy
  "Australian Centre for International Justice"
  "Government urged to screen Israeli nationals with a military background entering Australia ahead of Sydney Marathon"
  "28 August 2026"
  "ACIJ said at least 39 Israeli nationals were in Australia for the marathon, including people reportedly serving or having served in Gaza, the West Bank or Lebanon, and urged screening/referral where credible evidence existed"
  false

michaelWestPoliceEscortReceipt : ContemporarySourceReceipt
michaelWestPoliceEscortReceipt = contemporarySourceReceipt
  sixServingIDFRunnersPoliceProtectedReport investigativeJournalism
  "Andrew Brown, Michael West Media"
  "Sydney Marathon. Who told NSW Police to run bodyguard for Israel's army?"
  "3 September 2026"
  "Article reports six Israeli runners identified by a senior NSW police officer as serving IDF members received dedicated NSW Police running protection, with four to six police running alongside each; treat as journalistic reporting pending official records"
  false

nswPoliceMarathonOperationReceipt : ContemporarySourceReceipt
nswPoliceMarathonOperationReceipt = contemporarySourceReceipt
  generalMarathonHighVisibilityPoliceOperation abcReport
  "NSW Police Force"
  "Road closures begin ahead of 2026 Sydney Marathon"
  "28 August 2026"
  "NSW Police publicly announced a high-visibility marathon operation using general duties and specialist units; announcement did not disclose any dedicated IDF-runner protection detail"
  true

record ContemporaryBoundary : Set where
  constructor contemporaryBoundary
  field
    iranianWarshipMayBeRelabelledCivilianShip : Bool
    iranianWarshipMayBeRelabelledCivilianShipIsFalse : iranianWarshipMayBeRelabelledCivilianShip ≡ false
    australianPresenceProvesParticipationInTorpedoAttack : Bool
    australianPresenceProvesParticipationInTorpedoAttackIsFalse : australianPresenceProvesParticipationInTorpedoAttack ≡ false
    investigativeMarathonEscortReportEqualsOfficialPoliceAdmission : Bool
    investigativeMarathonEscortReportEqualsOfficialPoliceAdmissionIsFalse : investigativeMarathonEscortReportEqualsOfficialPoliceAdmission ≡ false
    militaryServiceHistoryEqualsIndividualWarCrimeLiability : Bool
    militaryServiceHistoryEqualsIndividualWarCrimeLiabilityIsFalse : militaryServiceHistoryEqualsIndividualWarCrimeLiability ≡ false

canonicalContemporaryBoundary : ContemporaryBoundary
canonicalContemporaryBoundary = contemporaryBoundary false refl false refl false refl false refl
