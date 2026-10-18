module DASHI.Wikimedia.MaboResidualDrivenProducerAdaptersValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact
open import DASHI.Wikimedia.LeanWikidataVerificationExact
open import DASHI.Wikimedia.JmdLeanGoldenAbiAttachmentExact
open import DASHI.Wikimedia.MaboLeanSlrP7dBidiBridgeExact
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

sampleObservation : WorldObservation
sampleObservation =
  mkWorldObservation
    "request:Q1501525:P710"
    "Q1501525"
    "P710"
    "wikidata"
    "wikidata:Q1501525:oldid:2333409615"
    "sha256:fixture"
    "Q975866"
    retrievalSucceeded
    currentFreshness
    statedInProvenance

sampleVerification : LeanVerificationReceipt
sampleVerification =
  leanVerificationReceipt
    sampleObservation
    encoded
    importFaithfullyRepresented
    checkPassed
    checkPassed
    exactSameObject
    relationAligned
    "lean:query:mabo:P710"
    "dashi_lean4@349f9b7dd49a7f23bfbd7d9da60416afa5440ccf"
    reportGenerated
    "csv:mabo-status"
    false
    false
    false

sampleJmdVerification : JmdVerificationAbiReceipt
sampleJmdVerification =
  mkJmdVerificationAbiReceipt
    sampleVerification
    "RequestProject.Cli.Derive.checkSubChain_sound"
    "receipt:jmd:mabo:P710"

sampleAttachment : LeanP7AttachmentReceipt
sampleAttachment =
  leanP7AttachmentReceipt
    "attachment:mabo:P710"
    sampleVerification
    "Q1501525"
    "P710"
    "wikidata:Q1501525:oldid:2333409615"
    "sha256:fixture"
    exactSameObject
    relationAligned
    false
    false
    false

sampleTypedAdapter : LeanVerifiedWikidataAdapterReceipt
sampleTypedAdapter =
  fromLeanVerificationToWikidataAdapter
    sampleVerification
    sampleAttachment
    "residual:mabo:identity"
    "identityResidual"

_ : parentQid sampleTypedAdapter ≡ "Q1501525"
_ = refl

_ : targetQid sampleTypedAdapter ≡ "Q975866"
_ = refl

_ : propertyReference sampleTypedAdapter ≡ "P710"
_ = refl

_ : sourceRevisionReference sampleTypedAdapter ≡
    "wikidata:Q1501525:oldid:2333409615"
_ = refl

_ : contentDigestReference sampleTypedAdapter ≡ "sha256:fixture"
_ = refl

_ : triggeringResidualReference sampleTypedAdapter ≡ "residual:mabo:identity"
_ = refl

_ : verificationCreatesExpansionCandidate sampleTypedAdapter ≡ false
_ = refl

sampleIntegratedAdapter : IntegratedLeanVerifiedWikidataAdapterReceipt
sampleIntegratedAdapter =
  fromJmdVerificationToIntegratedWikidataAdapter
    sampleJmdVerification
    sampleAttachment
    "residual:mabo:identity"
    "identityResidual"

_ : integratedAdapterUsesCanonicalJmdMachine sampleIntegratedAdapter ≡ true
_ = refl

_ : integratedAdapterCreatesExpansionCandidate sampleIntegratedAdapter ≡ false
_ = refl

_ : integratedAdapterCreatesSemanticAuthority sampleIntegratedAdapter ≡ false
_ = refl

_ : integratedAdapterCreatesClaimTruth sampleIntegratedAdapter ≡ false
_ = refl
