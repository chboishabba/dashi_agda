module DASHI.Law.SolomonIslandsDefeatMotionProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedPublicClaimExact as Public

------------------------------------------------------------------------
-- "DEFEAT THIS MOTION" PROVENANCE BOUNDARY
--
-- Correction after broader source review:
--   * the Australian High Commission -> Francis Sade communication carries
--     treaty/funding progress and "hold steady" language;
--   * separate reporting identifies the downstream coalition exhortation as
--     Sade's own message / a message believed to be from Sade to another
--     Solomon Islands MP.
--
-- Therefore the phrase "stand together to defeat this Motion" must NOT be
-- attributed to Jeffrey Roach or another Australian diplomatic actor absent a
-- stronger primary artifact.  The live question becomes a relay/conditionality
-- question, not a direct-Australian-instruction question.
------------------------------------------------------------------------

oppositionStatementViaSolomonStar : Public.PublicArtifactCitation
oppositionStatementViaSolomonStar = Public.public-artifact-citation
  "Office of the Leader of the Official Opposition, as reported by Solomon Star"
  "Opposition demands answers over claims of foreign interference, Government responds"
  "Solomon Star News"
  2026
  "https://www.solomonstarnews.com/opposition-demands-answers-over-claims-of-foreign-interference-government-responds/"
  "Opposition statement passages concerning prospective Australian assistance, treaty talks, and the phrase 'defeat this Motion'"
  Public.oppositionAllegation
  Public.institutionallyPublished
  "the Opposition says messages it saw paired prospective Australian assistance/treaty negotiations with an appeal for political unity to defeat the motion"

oppositionStatementViaPacificNews : Public.PublicArtifactCitation
oppositionStatementViaPacificNews = Public.public-artifact-citation
  "Office of the Leader of the Official Opposition, reproduced by Pacific regional news reporting"
  "Opposition demands answers over foreign interference in Solomon Islands domestic politics"
  "Pacific regional news syndication"
  2026
  "https://islandsbusiness.com/pacnews/pacnews-two-wednesday-9-september-2026/"
  "reproduced Opposition statement; subsequent-message sentence"
  Public.oppositionAllegation
  Public.institutionallyPublished
  "the reproduced Opposition statement says a subsequent message stated that the GREAT Coalition should stand together to defeat the motion"

sadeForwardingAndOwnMessageReport : Public.PublicArtifactCitation
sadeForwardingAndOwnMessageReport = Public.public-artifact-citation
  "Australian Associated Press, republished by National Indigenous Times"
  "Free education in $1b sweetener for Solomons treaty"
  "National Indigenous Times / Australian Associated Press"
  2026
  "https://nit.com.au/08-09-2026/26359/free-education-in-1b-sweetener-for-solomons-treaty"
  "reporting on leaked WhatsApp chain: Sade forwarding Australian High Commission update, followed by Sade's own coalition-directed message"
  Public.journalisticReport
  Public.institutionallyPublished
  "AAP reports the leaked WhatsApp message was sent by Francis Sade forwarding an Australian High Commission update, and separately characterises Sade's own message as aimed at wavering coalition MPs"

exactOppositionAttributedDefeatMotionClaim : Public.AttributedPublicClaim
exactOppositionAttributedDefeatMotionClaim = Public.attributed-public-claim
  oppositionStatementViaPacificNews
  "the Opposition publicly attributed to a subsequent message the statement that the GREAT Coalition should stand together to defeat the motion"
  true refl
  false refl

sadeRelayAttributionClaim : Public.AttributedPublicClaim
sadeRelayAttributionClaim = Public.attributed-public-claim
  sadeForwardingAndOwnMessageReport
  "AAP reports a two-stage communication: Sade forwarded the Australian High Commission treaty/funding update and Sade then sent his own coalition-directed political message"
  true refl
  false refl

------------------------------------------------------------------------
-- Sender classification.
------------------------------------------------------------------------

data ReportedSenderClass : Set where
  australianDiplomaticActor : ReportedSenderClass
  solomonIslandsDeputyPrimeMinister : ReportedSenderClass
  unresolvedSender : ReportedSenderClass

reportedDefeatMotionSenderClass : ReportedSenderClass
reportedDefeatMotionSenderClass = solomonIslandsDeputyPrimeMinister

------------------------------------------------------------------------
-- Authentication coordinates deliberately remain separate.
------------------------------------------------------------------------

data DefeatMotionCoordinate : Set where
  oppositionPublishedTheAllegation : DefeatMotionCoordinate
  underlyingMessageArtifactAcquired : DefeatMotionCoordinate
  underlyingMessageAuthenticated : DefeatMotionCoordinate
  downstreamSenderReportedAsSade : DefeatMotionCoordinate
  downstreamSenderPrimaryArtifactVerified : DefeatMotionCoordinate
  senderIsAustralianDiplomaticActor : DefeatMotionCoordinate
  highCommissionToSadeForwardingReported : DefeatMotionCoordinate
  exactThreadTopologyPrimaryVerified : DefeatMotionCoordinate

record CurrentDefeatMotionProvenance : Set where
  constructor current-defeat-motion-provenance
  field
    oppositionPublicationAvailable : Bool
    oppositionPublicationAvailableIsTrue : oppositionPublicationAvailable ≡ true
    exactReportedSentenceAvailable : Bool
    exactReportedSentenceAvailableIsTrue : exactReportedSentenceAvailable ≡ true
    downstreamSenderReportedAsSade : Bool
    downstreamSenderReportedAsSadeIsTrue : downstreamSenderReportedAsSade ≡ true
    highCommissionToSadeForwardingReported : Bool
    highCommissionToSadeForwardingReportedIsTrue : highCommissionToSadeForwardingReported ≡ true
    underlyingArtifactAcquired : Bool
    underlyingArtifactAcquiredIsFalse : underlyingArtifactAcquired ≡ false
    underlyingArtifactAuthenticated : Bool
    underlyingArtifactAuthenticatedIsFalse : underlyingArtifactAuthenticated ≡ false
    exactThreadTopologyPrimaryVerified : Bool
    exactThreadTopologyPrimaryVerifiedIsFalse : exactThreadTopologyPrimaryVerified ≡ false
    directAustralianDefeatMotionInstructionEstablished : Bool
    directAustralianDefeatMotionInstructionEstablishedIsFalse :
      directAustralianDefeatMotionInstructionEstablished ≡ false
    nextAcquisition : String

open CurrentDefeatMotionProvenance public

currentDefeatMotionProvenance : CurrentDefeatMotionProvenance
currentDefeatMotionProvenance = current-defeat-motion-provenance
  true refl
  true refl
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
  "Acquire the original WhatsApp/thread artifact or an independently authenticated reproduction sufficient to establish timestamps, forwarding boundaries, exact sender/recipient identities and whether Sade's coalition exhortation was textually or conditionally linked to the Australian High Commission update"

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data OppositionQuoteAuthenticatesUnderlyingArtifact : Set where
data SadeForwardingMakesSadeMessageAustralianSpeech : Set where
data AustralianFundingUpdateImpliesAustralianDefeatInstruction : Set where
data SameThreadImpliesSharedIntent : Set where

a oppositionQuoteDoesNotAuthenticateArtifact :
  OppositionQuoteAuthenticatesUnderlyingArtifact → ⊥
a oppositionQuoteDoesNotAuthenticateArtifact ()

sadeForwardDoesNotTransferAuthorship :
  SadeForwardingMakesSadeMessageAustralianSpeech → ⊥
sadeForwardDoesNotTransferAuthorship ()

fundingUpdateDoesNotBecomeDefeatInstruction :
  AustralianFundingUpdateImpliesAustralianDefeatInstruction → ⊥
fundingUpdateDoesNotBecomeDefeatInstruction ()

sameThreadDoesNotEstablishSharedIntent : SameThreadImpliesSharedIntent → ⊥
sameThreadDoesNotEstablishSharedIntent ()
