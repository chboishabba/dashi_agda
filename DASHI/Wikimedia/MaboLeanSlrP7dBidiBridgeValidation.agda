module DASHI.Wikimedia.MaboLeanSlrP7dBidiBridgeValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])

open import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact
open import DASHI.Wikimedia.LeanWikidataVerificationExact
open import DASHI.Wikimedia.MaboLeanSlrP7dBidiBridgeExact

sampleObservation : WorldObservation
sampleObservation =
  mkWorldObservation
    "request:mabo:P710"
    "Q1501525"
    "P710"
    "wikidata"
    "wikidata:Q1501525:oldid:2333409615"
    "sha256:fixture"
    "Q975866"
    retrievalSucceeded
    staleFreshness
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
    "jmd-aristotle:lean4-v4.28.0"
    reportGenerated
    "csv:mabo-status"
    false
    false
    false

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

_ : attachmentCreatesExpansionCandidate sampleAttachment ≡ false
_ = refl

_ : attachmentCreatesSemanticAuthority sampleAttachment ≡ false
_ = refl

sampleFreshnessReopening : FreshnessReopeningReceipt
sampleFreshnessReopening =
  freshnessReopeningReceipt
    "freshness-reopen:mabo:P710"
    sampleVerification
    "wikidata:Q1501525:current"
    true
    false
    false

_ : currentApplicabilityReopened sampleFreshnessReopening ≡ true
_ = refl

_ : historicalKernelReceiptNegated sampleFreshnessReopening ≡ false
_ = refl

_ : predictedContractionEqualsObservedByDefinition canonicalP7dBidiBoundary ≡ false
_ = refl

_ : kernelPassedCreatesAdmission canonicalP7dBidiBoundary ≡ false
_ = refl

_ : admissionCreatesClaimTruth canonicalP7dBidiBoundary ≡ false
_ = refl

_ : representationIdentityEqualsWorldIdentity canonicalP7dBidiBoundary ≡ false
_ = refl

_ : derivationalNoveltyCountsAsExternalWorldNovelty canonicalP7dBidiBoundary ≡ false
_ = refl
