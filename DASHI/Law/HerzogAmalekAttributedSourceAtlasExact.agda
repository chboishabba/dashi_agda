module DASHI.Law.HerzogAmalekAttributedSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as SearchBridge

------------------------------------------------------------------------
-- HERZOG / AMALEK ATTRIBUTED SOURCE LAYERS
--
-- Existing proposition/role-binding owners remain authoritative for DASHI's
-- formal distinctions. This atlas only normalises recoverable source identity.
-- Original speech, party filing, judicial observation, parliamentary record,
-- police-owned recording and media publication remain distinct source layers.
------------------------------------------------------------------------

netanyahu28OctoberPMO : Source.AttributedSource
netanyahu28OctoberPMO = Source.mkNoDOISource
  "Benjamin Netanyahu / Prime Minister's Office, State of Israel"
  "Statement by PM Netanyahu"
  "Prime Minister's Office, Government of Israel"
  "2023"
  "https://www.gov.il/en/pages/statement-by-pm-netanyahu-28-oct-2023"
  Source.governmentSource
  "primary executive-speech carrier identity for the 28 October 2023 address; current tool access returned 403, so exact text inspection remains a separate diligence obligation"
  Source.publicAttribution

southAfricaICJApplication2023 : Source.AttributedSource
southAfricaICJApplication2023 = Source.mkNoDOISource
  "Republic of South Africa"
  "Application instituting proceedings and request for the indication of provisional measures"
  "International Court of Justice, South Africa v. Israel, General List No. 192"
  "2023"
  "https://www.icj-cij.org/node/203394"
  Source.governmentSource
  "primary party filing for South Africa's allegations, quotations and legal characterisation; party pleading is not a judicial merits finding and is not the original carrier of quoted executive speech"
  Source.publicAttribution

judgeNolteDeclaration2024 : Source.AttributedSource
judgeNolteDeclaration2024 = Source.mkNoDOISource
  "Judge Georg Nolte"
  "Declaration of Judge Nolte"
  "International Court of Justice, Order of 26 January 2024, South Africa v. Israel"
  "2024"
  "https://www.icj-cij.org/node/203451"
  Source.governmentSource
  "primary judicial declaration in provisional-measures proceedings; supports the bounded judicial observation about threatening echoes of inflammatory statements, not a final merits determination"
  Source.publicAttribution

knessetBibasMemorial2025 : Source.AttributedSource
knessetBibasMemorial2025 = Source.mkNoDOISource
  "The Knesset / Speaker Amir Ohana"
  "Knesset observes moment of silence in memory of Bibas family members, Oded Lifshitz and all those slain and fallen since October 7; Knesset building illuminated in orange as tribute"
  "Knesset News"
  "2025"
  "https://main.knesset.gov.il/EN/News/PressReleases/Pages/press26225q.aspx"
  Source.governmentSource
  "primary parliamentary record for the 26 February 2025 memorial remarks; the record supports only the utterances/context it contains"
  Source.publicAttribution

guardianHerzogBodycam2026 : Source.AttributedSource
guardianHerzogBodycam2026 = Source.mkNoDOISource
  "The Guardian"
  "Footage of police officer boasting about punching Sydney anti-Herzog protester raises questions about conduct"
  "Guardian Australia"
  "2026"
  "https://www.theguardian.com/australia-news/2026/sep/01/police-officer-boasted-about-punching-anti-herzog-protester-when-he-was-down-bodycam-footage-reveals-ntwnfb"
  Source.newsSource
  "secondary journalistic publication carrying leaked NSW Police body-worn-camera footage; the underlying police-owned recording remains a distinct primary artifact and lawfulness/motive/policy remain downstream questions"
  Source.publicAttribution

guardianHerzogBodycamVideo2026 : Source.AttributedSource
guardianHerzogBodycamVideo2026 = Source.mkNoDOISource
  "The Guardian / supplied leaked footage"
  "Footage shows NSW police officer boasting about 'punching' anti-Herzog protester in head – video"
  "Guardian Australia"
  "2026"
  "https://www.theguardian.com/australia-news/video/2026/sep/01/footage-nsw-police-officer-boast-punch-anti-herzog-protester-video-ntwnfb"
  Source.newsSource
  "media-hosted copy of leaked body-worn-camera footage; stronger than a prose recollection for recorded utterances, but not identical to police custody/provenance of the original recording"
  Source.publicAttribution

herzogAmalekSourceAtlas : Source.AttributedSourceAtlas
herzogAmalekSourceAtlas = Source.mkSourceAtlas
  "Herzog / contemporary Amalek layered source atlas"
  "DASHI.Law.HerzogAmalekAttributedSourceAtlasExact"
  (netanyahu28OctoberPMO
    ∷ southAfricaICJApplication2023
    ∷ judgeNolteDeclaration2024
    ∷ knessetBibasMemorial2025
    ∷ guardianHerzogBodycam2026
    ∷ guardianHerzogBodycamVideo2026
    ∷ [])
  "normalises recoverable source identities while preserving executive speech, party pleading, judicial declaration, parliamentary record, police recording and media publication as different provenance layers"

------------------------------------------------------------------------
-- Explicit remaining source-diligence residuals.
------------------------------------------------------------------------

record UnresolvedPrimaryCarrier : Set where
  constructor unresolved-primary-carrier
  field
    claimReference : String
    knownSecondaryOrDerivativeReference : String
    missingCoordinate : SearchBridge.SourceDiligenceGap
    nextProducer : SearchBridge.SourceDiligenceGap
    residualReference : String

open UnresolvedPrimaryCarrier public

netanyahu3NovemberLetterPrimaryResidual : UnresolvedPrimaryCarrier
netanyahu3NovemberLetterPrimaryResidual = unresolved-primary-carrier
  "Netanyahu 3 November 2023 public letter to Israeli soldiers and commanders invoked the Amalek remembrance verse"
  "reported/quoted by later sources including the ICJ party filing; exact original PMO carrier must be inspected directly"
  SearchBridge.missingExactLocator
  SearchBridge.primarySourceNotSearched
  "retain role-binding proposition as source-backed at its current evidence level; do not silently identify a derivative quotation with the original government artifact"

herzogBodycamOriginalCustodyResidual : UnresolvedPrimaryCarrier
herzogBodycamOriginalCustodyResidual = unresolved-primary-carrier
  "literal utterances recorded on NSW Police body-worn camera during the 9 February 2026 anti-Herzog operation"
  "Guardian-hosted leaked copy, 1 September 2026"
  SearchBridge.sameObjectUnresolved
  SearchBridge.primarySourceNotSearched
  "media-hosted footage can support bounded recorded-utterance analysis, while original police custody/hash/full sequence remain distinct primary-evidence coordinates"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PartyPleadingIsJudicialFinding : Set where
data JudicialProvisionalObservationIsFinalMeritsFinding : Set where
data MediaHostedLeakEqualsOriginalPoliceCustody : Set where
data AmalekRoleBindingProvesLiteralGroupIdentity : Set where

partyPleadingRemainsPartyPleading : PartyPleadingIsJudicialFinding → ⊥
partyPleadingRemainsPartyPleading ()

provisionalObservationDoesNotBecomeFinalMerits :
  JudicialProvisionalObservationIsFinalMeritsFinding → ⊥
provisionalObservationDoesNotBecomeFinalMerits ()

mediaCopyDoesNotErasePrimaryCustody : MediaHostedLeakEqualsOriginalPoliceCustody → ⊥
mediaCopyDoesNotErasePrimaryCustody ()

roleBindingStillDoesNotCreateLiteralIdentity :
  AmalekRoleBindingProvesLiteralGroupIdentity → ⊥
roleBindingStillDoesNotCreateLiteralIdentity ()
