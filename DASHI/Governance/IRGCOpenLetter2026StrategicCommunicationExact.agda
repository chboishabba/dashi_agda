module DASHI.Governance.IRGCOpenLetter2026StrategicCommunicationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Typed strategic-communication surface.
--
-- This module formalises SOURCE STRUCTURE, not a political verdict.
-- In particular, Says source p is deliberately distinct from p.
------------------------------------------------------------------------

data Actor : Set where
  irgc americanPeople americanGovernment iranianPeople
  americanPoliticalElite unnamedWorldPublic : Actor

data Audience : Set where
  usPublic scholars students journalists generalAudience : Audience

data ClaimKind : Set where
  empirical theological historical evaluative predictive attributional : ClaimKind

data SpeechAct : Set where
  assertion accusation prediction warning appeal exhortation
  moralAnalogy identityReframing solidarityOffer conditionalCoexistence : SpeechAct

data RhetoricalRole : Set where
  peopleStateSeparation commonOppressorFrame sharedVictimFrame
  agencyAttribution coexistenceFrame liberationFrame
  scripturalEthicalBridge eschatologicalClosure : RhetoricalRole

data Tradition : Set where
  islam christianity judaism : Tradition

data NormativeText : Set where
  quran13_11 quran21_105 matthew7_12 luke6_31 jeremiah18_7_10 talmudicGoldenRule : NormativeText

record Artifact : Set where
  constructor artifact
  field
    issuer : Actor
    audience : Audience
    title : String
    date : String
    primaryReceipt : String

open Artifact public

irgcLetter : Artifact
irgcLetter = artifact
  irgc usPublic
  "IRGC open letter to the people of the United States"
  "2026-09-29"
  "IRGC 2026 primary English PDF"

record AttributedClaim : Set where
  constructor attributedClaim
  field
    claimId : String
    kind : ClaimKind
    assertedBy : Actor
    content : String
    sourceReceipt : String
    independentlyEstablished : Bool

open AttributedClaim public

mkSourceLocalClaim : String → ClaimKind → Actor → String → String → AttributedClaim
mkSourceLocalClaim id kind speaker content receipt =
  attributedClaim id kind speaker content receipt false

publicationDoesNotPromoteTruth :
  (claim : AttributedClaim) →
  independentlyEstablished claim ≡ false
publicationDoesNotPromoteTruth claim = refl

record Segment : Set where
  constructor segment
  field
    segmentId : String
    speechActs : List SpeechAct
    roles : List RhetoricalRole
    sourceReceipt : String

record CrossTraditionCitation : Set where
  constructor crossTraditionCitation
  field
    tradition : Tradition
    sourceText : NormativeText
    locator : String
    invokedPrinciple : String
    receipt : String
    doctrinalIdentityEstablished : Bool

open CrossTraditionCitation public

mkInvocation :
  Tradition → NormativeText → String → String → String →
  CrossTraditionCitation
mkInvocation tradition text locator principle receipt =
  crossTraditionCitation tradition text locator principle receipt false

invocationDoesNotEstablishDoctrinalIdentity :
  (citation : CrossTraditionCitation) →
  doctrinalIdentityEstablished citation ≡ false
invocationDoesNotEstablishDoctrinalIdentity citation = refl

quranAgency : CrossTraditionCitation
quranAgency = mkInvocation islam quran13_11 "Qur'an 13:11"
  "people changing their own condition / affairs"
  "opening citation in primary PDF"

matthewReciprocity : CrossTraditionCitation
matthewReciprocity = mkInvocation christianity matthew7_12 "Matthew 7:12"
  "reciprocity / treatment of others"
  "cross-tradition citation in primary PDF"

lukeReciprocity : CrossTraditionCitation
lukeReciprocity = mkInvocation christianity luke6_31 "Luke 6:31"
  "reciprocity / treatment of others"
  "cross-tradition citation in primary PDF"

jeremiahConditionality : CrossTraditionCitation
jeremiahConditionality = mkInvocation christianity jeremiah18_7_10 "Jeremiah 18:7-10"
  "conditional judgement and change"
  "cross-tradition citation in primary PDF"

talmudicReciprocity : CrossTraditionCitation
talmudicReciprocity = mkInvocation judaism talmudicGoldenRule "Talmudic reciprocity citation as rendered by source"
  "do not do to another what is hateful to you"
  "cross-tradition citation in primary PDF"

quranClosure : CrossTraditionCitation
quranClosure = mkInvocation islam quran21_105 "Qur'an 21:105"
  "inheritance of the earth by the righteous / servants"
  "closing citation in primary PDF"

record AudienceEffectEvidence : Set where
  constructor audienceEffectEvidence
  field
    observedPopulation : String
    measuredOutcome : String
    receipt : String

data AudienceEffectEstablished : Set where

publicationAloneCannotEstablishAudienceEffect :
  Artifact → AudienceEffectEstablished → ⊥
publicationAloneCannotEstablishAudienceEffect artifact ()
