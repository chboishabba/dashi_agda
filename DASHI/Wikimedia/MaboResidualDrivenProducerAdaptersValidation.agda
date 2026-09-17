module DASHI.Wikimedia.MaboResidualDrivenProducerAdaptersValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Wikimedia.MaboResidualDrivenProducerAdaptersExact

_ : oalcProducesPrimaryLegalSource canonicalProducerAdapterBoundary ≡ true
_ = refl

_ : wikidataProducesQid canonicalProducerAdapterBoundary ≡ true
_ = refl

_ : wikipediaRequiresAcquiredRevision canonicalProducerAdapterBoundary ≡ true
_ = refl

_ : producerDeterminesResidualClass canonicalProducerAdapterBoundary ≡ false
_ = refl

_ : reachableArticleRouteEqualsAcquiredArticle canonicalProducerAdapterBoundary ≡ false
_ = refl

_ : adapterCreatesSemanticAuthority canonicalProducerAdapterBoundary ≡ false
_ = refl

_ : adapterCreatesClaimTruth canonicalProducerAdapterBoundary ≡ false
_ = refl
