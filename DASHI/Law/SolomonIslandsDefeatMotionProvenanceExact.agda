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
-- Public reporting now reproduces the Opposition's assertion that a subsequent
-- message stated: "Reflecting on the meaningful reforms the GREAT Coalition has
-- already begun, we need to stand together to defeat this Motion."
--
-- This module records that exact proposition as an Opposition-attributed claim.
-- It does NOT authenticate the underlying message, identify its sender, or prove
-- that the speaker was an Australian diplomatic actor.
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

exactOppositionAttributedDefeatMotionClaim : Public.AttributedPublicClaim
exactOppositionAttributedDefeatMotionClaim = Public.attributed-public-claim
  oppositionStatementViaPacificNews
  "the Opposition publicly attributed to a subsequent message the statement that the GREAT Coalition should stand together to defeat the motion"
  true refl
  false refl

------------------------------------------------------------------------
-- Authentication coordinates deliberately remain separate.
------------------------------------------------------------------------

data DefeatMotionCoordinate : Set where
  oppositionPublishedTheAllegation : DefeatMotionCoordinate
  underlyingMessageArtifactAcquired : DefeatMotionCoordinate
  underlyingMessageAuthenticated : DefeatMotionCoordinate
  underlyingMessageSenderIdentified : DefeatMotionCoordinate
  senderIsAustralianDiplomaticActor : DefeatMotionCoordinate
  messageLinkedToFundingCommunicationChain : DefeatMotionCoordinate

record CurrentDefeatMotionProvenance : Set where
  constructor current-defeat-motion-provenance
  field
    oppositionPublicationAvailable : Bool
    oppositionPublicationAvailableIsTrue : oppositionPublicationAvailable ≡ true
    exactReportedSentenceAvailable : Bool
    exactReportedSentenceAvailableIsTrue : exactReportedSentenceAvailable ≡ true
    underlyingArtifactAcquired : Bool
    underlyingArtifactAcquiredIsFalse : underlyingArtifactAcquired ≡ false
    underlyingArtifactAuthenticated : Bool
    underlyingArtifactAuthenticatedIsFalse : underlyingArtifactAuthenticated ≡ false
    senderIdentityResolved : Bool
    senderIdentityResolvedIsFalse : senderIdentityResolved ≡ false
    australianActorAttributionResolved : Bool
    australianActorAttributionResolvedIsFalse : australianActorAttributionResolved ≡ false
    sameCommunicationChainResolved : Bool
    sameCommunicationChainResolvedIsFalse : sameCommunicationChainResolved ≡ false
    nextAcquisition : String

open CurrentDefeatMotionProvenance public

currentDefeatMotionProvenance : CurrentDefeatMotionProvenance
currentDefeatMotionProvenance = current-defeat-motion-provenance
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl
  "Acquire the original message/thread or an independently authenticated reproduction sufficient to identify sender, recipient, timestamp, and relationship to the already ABC-authenticated Roach communication"

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data OppositionQuoteAuthenticatesUnderlyingArtifact : Set where
data ReportedSentenceIdentifiesAustralianSender : Set where
data SameTopicMeansSameMessageChain : Set where

oppositionQuoteDoesNotAuthenticateArtifact :
  OppositionQuoteAuthenticatesUnderlyingArtifact → ⊥
oppositionQuoteDoesNotAuthenticateArtifact ()

reportedSentenceDoesNotIdentifyAustralianSender :
  ReportedSentenceIdentifiesAustralianSender → ⊥
reportedSentenceDoesNotIdentifyAustralianSender ()

sameTopicDoesNotEstablishSameChain : SameTopicMeansSameMessageChain → ⊥
sameTopicDoesNotEstablishSameChain ()
