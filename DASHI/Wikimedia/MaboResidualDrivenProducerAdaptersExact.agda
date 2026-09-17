module DASHI.Wikimedia.MaboResidualDrivenProducerAdaptersExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboResidualDrivenWorldExpansionExact
import DASHI.Wikimedia.MaboResidualDrivenWorldExpansionStepExact
import DASHI.Wikimedia.MaboReviewedContextFederationExact
import DASHI.Wikimedia.SLRWikimediaHandoffABIExact

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
  producerAdapterBoundary
    true
    true
    true
    false
    false
    false
    false

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
-- Non-collapse firewalls.
------------------------------------------------------------------------

data ProducerIdentityDeterminesResidualClass : Set where
data ReachableWikipediaRouteEqualsAcquiredArticle : Set where
data AdapterProjectionEqualsSemanticAuthority : Set where
data AdapterProjectionEqualsClaimTruth : Set where

producerIdentityDoesNotDetermineResidualClass :
  ProducerIdentityDeterminesResidualClass → ⊥
producerIdentityDoesNotDetermineResidualClass ()

reachableWikipediaRouteDoesNotEqualAcquiredArticle :
  ReachableWikipediaRouteEqualsAcquiredArticle → ⊥
reachableWikipediaRouteDoesNotEqualAcquiredArticle ()

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
-- Wikidata property route + pinned entity revision -> QID candidate
-- acquired Wikipedia source + revision/hash -> article candidate
--
-- In every lane, the triggering residual class remains supplied by the PNF /
-- world diagnosis rather than inferred from producer identity. Adapter output is
-- still candidate-only and grants neither semantic authority nor claim truth.
------------------------------------------------------------------------
