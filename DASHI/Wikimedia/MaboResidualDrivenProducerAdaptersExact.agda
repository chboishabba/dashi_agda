module DASHI.Wikimedia.MaboResidualDrivenProducerAdaptersExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboResidualDrivenWorldExpansionExact
import DASHI.Wikimedia.MaboResidualDrivenWorldExpansionStepExact
import DASHI.Wikimedia.MaboReviewedContextFederationExact
import DASHI.Wikimedia.SLRWikimediaHandoffABIExact
import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact as Observation
import DASHI.Wikimedia.LeanWikidataVerificationExact as Verification
import DASHI.Wikimedia.JmdLeanGoldenAbiAttachmentExact as Jmd
import DASHI.Wikimedia.MaboLeanSlrP7dBidiBridgeExact as Bidi

record ProducerAdapterBoundary : Set where
  constructor producerAdapterBoundary
  field
    oalcProducesPrimaryLegalSource : Bool
    wikidataProducesQid : Bool
    wikipediaRequiresAcquiredRevision : Bool
    producerDeterminesResidualClass : Bool
    reachableArticleRouteEqualsAcquiredArticle : Bool
    adapterCreatesSemanticAuthority : Bool
    adapterCreatesClaimTruth : Bool

open ProducerAdapterBoundary public

canonicalProducerAdapterBoundary : ProducerAdapterBoundary
canonicalProducerAdapterBoundary =
  producerAdapterBoundary true true true false false false false

oalcProducesPrimaryLegalSourceTrue :
  oalcProducesPrimaryLegalSource canonicalProducerAdapterBoundary ≡ true
oalcProducesPrimaryLegalSourceTrue = refl

wikidataProducesQidTrue :
  wikidataProducesQid canonicalProducerAdapterBoundary ≡ true
wikidataProducesQidTrue = refl

wikipediaRequiresAcquiredRevisionTrue :
  wikipediaRequiresAcquiredRevision canonicalProducerAdapterBoundary ≡ true
wikipediaRequiresAcquiredRevisionTrue = refl

producerDeterminesResidualClassFalse :
  producerDeterminesResidualClass canonicalProducerAdapterBoundary ≡ false
producerDeterminesResidualClassFalse = refl

reachableArticleRouteEqualsAcquiredArticleFalse :
  reachableArticleRouteEqualsAcquiredArticle canonicalProducerAdapterBoundary ≡ false
reachableArticleRouteEqualsAcquiredArticleFalse = refl

adapterCreatesSemanticAuthorityFalse :
  adapterCreatesSemanticAuthority canonicalProducerAdapterBoundary ≡ false
adapterCreatesSemanticAuthorityFalse = refl

adapterCreatesClaimTruthFalse :
  adapterCreatesClaimTruth canonicalProducerAdapterBoundary ≡ false
adapterCreatesClaimTruthFalse = refl

------------------------------------------------------------------------
-- TYPED LEAN/WIKIDATA VERIFICATION ATTACHMENT FOR THE P7d.1 LANE
------------------------------------------------------------------------

record LeanVerifiedWikidataAdapterReceipt : Set where
  constructor lean-verified-wikidata-adapter-receipt
  field
    verificationReceipt : Verification.LeanVerificationReceipt
    attachmentReceipt : Bidi.LeanP7AttachmentReceipt
    parentQid : String
    targetQid : String
    propertyReference : String
    sourceRevisionReference : String
    contentDigestReference : String
    triggeringResidualReference : String
    residualClassReference : String
    verificationCreatesExpansionCandidate : Bool
    typedAdapterCreatesSemanticAuthority : Bool
    typedAdapterCreatesClaimTruth : Bool

open LeanVerifiedWikidataAdapterReceipt public

fromLeanVerificationToWikidataAdapter :
  Verification.LeanVerificationReceipt →
  Bidi.LeanP7AttachmentReceipt →
  String →
  String →
  LeanVerifiedWikidataAdapterReceipt
fromLeanVerificationToWikidataAdapter verification attachment residual residualClass =
  lean-verified-wikidata-adapter-receipt
    verification
    attachment
    (Observation.objectReference observation)
    (Observation.observedValueReference observation)
    (Observation.relationReference observation)
    (Observation.sourceRevisionReference observation)
    (Observation.contentDigestReference observation)
    residual
    residualClass
    false false false
  where
    observation : Observation.WorldObservation
    observation = Verification.verificationObservation verification

------------------------------------------------------------------------
-- CANONICAL INTEGRATED-MACHINE WRAPPER
--
-- This is the preferred JMD lane after dashi_lean4@349f9b7d integrated the
-- Aristotle machine.  The legacy raw-verification adapter remains available as
-- a generic golden ABI, while this wrapper retains the concrete JMD declaration
-- and repository-generation attachment supplied by JmdVerificationAbiReceipt.
------------------------------------------------------------------------

record IntegratedLeanVerifiedWikidataAdapterReceipt : Set where
  constructor integrated-lean-verified-wikidata-adapter-receipt
  field
    jmdVerificationReceipt : Jmd.JmdVerificationAbiReceipt
    baseWikidataAdapterReceipt : LeanVerifiedWikidataAdapterReceipt
    integratedAdapterUsesCanonicalJmdMachine : Bool
    integratedAdapterCreatesExpansionCandidate : Bool
    integratedAdapterCreatesSemanticAuthority : Bool
    integratedAdapterCreatesClaimTruth : Bool

open IntegratedLeanVerifiedWikidataAdapterReceipt public

fromJmdVerificationToIntegratedWikidataAdapter :
  Jmd.JmdVerificationAbiReceipt →
  Bidi.LeanP7AttachmentReceipt →
  String →
  String →
  IntegratedLeanVerifiedWikidataAdapterReceipt
fromJmdVerificationToIntegratedWikidataAdapter jmdVerification attachment residual residualClass =
  integrated-lean-verified-wikidata-adapter-receipt
    jmdVerification
    (fromLeanVerificationToWikidataAdapter
      (Jmd.attachedVerification jmdVerification)
      attachment
      residual
      residualClass)
    true
    false
    false
    false

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data ProducerIdentityDeterminesResidualClass : Set where
data ReachableWikipediaRouteEqualsAcquiredArticle : Set where
data ReachableWikidataRouteEqualsAcquiredRevisionedEntity : Set where
data LeanVerificationEqualsExpansionCandidate : Set where
data JmdVerificationReceiptEqualsExpansionCandidate : Set where
data AdapterProjectionEqualsSemanticAuthority : Set where
data AdapterProjectionEqualsClaimTruth : Set where

producerIdentityDoesNotDetermineResidualClass :
  ProducerIdentityDeterminesResidualClass → ⊥
producerIdentityDoesNotDetermineResidualClass ()

reachableWikipediaRouteDoesNotEqualAcquiredArticle :
  ReachableWikipediaRouteEqualsAcquiredArticle → ⊥
reachableWikipediaRouteDoesNotEqualAcquiredArticle ()

reachableWikidataRouteDoesNotEqualAcquiredRevisionedEntity :
  ReachableWikidataRouteEqualsAcquiredRevisionedEntity → ⊥
reachableWikidataRouteDoesNotEqualAcquiredRevisionedEntity ()

leanVerificationDoesNotEqualExpansionCandidate :
  LeanVerificationEqualsExpansionCandidate → ⊥
leanVerificationDoesNotEqualExpansionCandidate ()

jmdVerificationReceiptDoesNotEqualExpansionCandidate :
  JmdVerificationReceiptEqualsExpansionCandidate → ⊥
jmdVerificationReceiptDoesNotEqualExpansionCandidate ()

adapterProjectionDoesNotEqualSemanticAuthority :
  AdapterProjectionEqualsSemanticAuthority → ⊥
adapterProjectionDoesNotEqualSemanticAuthority ()

adapterProjectionDoesNotEqualClaimTruth :
  AdapterProjectionEqualsClaimTruth → ⊥
adapterProjectionDoesNotEqualClaimTruth ()

------------------------------------------------------------------------
-- Runtime parity interpretation
--
-- OALC exact lookup receipt -> primary legal-source candidate
-- acquired/revisioned Wikidata entity + property route -> QID candidate
-- acquired Wikipedia source + revision/hash -> article candidate
--
-- JMD Lean verification is attached as independent executable-machine metadata;
-- it neither creates the external ExpansionCandidate nor determines residual
-- class, semantic authority or claim truth.
------------------------------------------------------------------------
