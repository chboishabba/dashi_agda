module DASHI.Law.SolomonIslandsDefeatMotionRepublicationIndependenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedPublicClaimExact as Public
import DASHI.Law.SolomonIslandsDefeatMotionProvenanceExact as Defeat

------------------------------------------------------------------------
-- REPUBLICATION != INDEPENDENT AUTHENTICATION
--
-- Several outlets reproduce the Opposition statement and the quoted
-- defeat-motion sentence.  That increases recoverability of the public
-- allegation but does not create multiple independent authentications of the
-- underlying message artifact.
------------------------------------------------------------------------

data PublicationRelation : Set where
  originatingStatement : PublicationRelation
  directRepublication : PublicationRelation
  journalisticReportOfStatement : PublicationRelation
  independentlyInspectedArtifact : PublicationRelation

record PublicationWitness : Set where
  constructor publication-witness
  field
    source : Public.PublicArtifactCitation
    relation : PublicationRelation
    reproducesDefeatMotionSentence : Bool
    reproducesDefeatMotionSentenceIsTrue : reproducesDefeatMotionSentence ≡ true
    independentlyAuthenticatedUnderlyingArtifact : Bool
    independentlyAuthenticatedUnderlyingArtifactIsFalse :
      independentlyAuthenticatedUnderlyingArtifact ≡ false

open PublicationWitness public

solomonStarRepublication : Public.PublicArtifactCitation
solomonStarRepublication = Public.public-artifact-citation
  "Solomon Star News"
  "Opposition demands answers over claims of foreign interference, Government responds"
  "Solomon Star News"
  2026
  "https://www.solomonstarnews.com/opposition-demands-answers-over-claims-of-foreign-interference-government-responds/"
  "Opposition statement passages reproducing the alleged subsequent-message sentence"
  Public.journalisticReport
  Public.institutionallyPublished
  "Reproduces the Opposition allegation and quoted defeat-motion sentence; does not independently authenticate the underlying message artifact"

tavuliRepublication : Public.PublicArtifactCitation
tavuliRepublication = Public.public-artifact-citation
  "Tavuli News"
  "Opposition Demands Answers Over Apparent Foreign Interference in Solomon Islands Politics"
  "Tavuli News"
  2026
  "https://www.tavulinews.com.sb/opposition-demands-answers-foreign-interference-solomon-islands-politics/"
  "Opposition statement passages reproducing the alleged subsequent-message sentence"
  Public.journalisticReport
  Public.institutionallyPublished
  "Reproduces the Opposition allegation and quoted defeat-motion sentence; does not independently authenticate the underlying message artifact"

pacnewsRepublication : Public.PublicArtifactCitation
pacnewsRepublication = Public.public-artifact-citation
  "PACNEWS / Islands Business"
  "Opposition demands answers over foreign interference in Solomon Islands domestic politics"
  "Islands Business PACNEWS feed"
  2026
  "https://islandsbusiness.com/pacnews/pacnews-two-wednesday-9-september-2026/"
  "PACNEWS item reproducing the Opposition statement and defeat-motion sentence"
  Public.journalisticReport
  Public.institutionallyPublished
  "Reproduces the Opposition allegation and quoted defeat-motion sentence; does not independently authenticate the underlying message artifact"

solomonStarWitness : PublicationWitness
solomonStarWitness = publication-witness
  solomonStarRepublication
  journalisticReportOfStatement
  true refl
  false refl

tavuliWitness : PublicationWitness
tavuliWitness = publication-witness
  tavuliRepublication
  directRepublication
  true refl
  false refl

pacnewsWitness : PublicationWitness
pacnewsWitness = publication-witness
  pacnewsRepublication
  directRepublication
  true refl
  false refl

------------------------------------------------------------------------
-- Corroboration coordinates.
------------------------------------------------------------------------

record CurrentRepublicationState : Set where
  constructor current-republication-state
  field
    publicSentenceRecoverableAcrossMultiplePublishers : Bool
    publicSentenceRecoverableAcrossMultiplePublishersIsTrue :
      publicSentenceRecoverableAcrossMultiplePublishers ≡ true
    independentUnderlyingArtifactAuthenticationAvailable : Bool
    independentUnderlyingArtifactAuthenticationAvailableIsFalse :
      independentUnderlyingArtifactAuthenticationAvailable ≡ false
    sameSenderAsABCAuthenticatedRoachMessageEstablished : Bool
    sameSenderAsABCAuthenticatedRoachMessageEstablishedIsFalse :
      sameSenderAsABCAuthenticatedRoachMessageEstablished ≡ false

open CurrentRepublicationState public

currentRepublicationState : CurrentRepublicationState
currentRepublicationState = current-republication-state
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data MultipleRepublicationsEqualIndependentAuthentication : Set where
data QuotedSentenceEqualPrimaryArtifact : Set where
data SharedWordingEstablishesSharedSender : Set where

republicationMultiplicityDoesNotAuthenticateArtifact :
  MultipleRepublicationsEqualIndependentAuthentication → ⊥
republicationMultiplicityDoesNotAuthenticateArtifact ()

quotedSentenceDoesNotBecomePrimaryArtifact : QuotedSentenceEqualPrimaryArtifact → ⊥
quotedSentenceDoesNotBecomePrimaryArtifact ()

sharedWordingDoesNotEstablishSharedSender : SharedWordingEstablishesSharedSender → ⊥
sharedWordingDoesNotEstablishSharedSender ()
