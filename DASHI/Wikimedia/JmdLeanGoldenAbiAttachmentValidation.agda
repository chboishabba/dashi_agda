module DASHI.Wikimedia.JmdLeanGoldenAbiAttachmentValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact
open import DASHI.Wikimedia.LeanWikidataVerificationExact
open import DASHI.Wikimedia.JmdLeanGoldenAbiAttachmentExact

_ : getterSurfaceUsesIntegratedMachine canonicalJmdGetterSurface ≡ true
_ = refl

_ : verificationSurfaceUsesIntegratedMachine canonicalJmdVerificationSurface ≡ true
_ = refl

_ : publicationSurfaceUsesIntegratedMachine canonicalJmdPublicationSurface ≡ true
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

sampleGetterReceipt : JmdGetterAbiReceipt
sampleGetterReceipt =
  mkJmdGetterAbiReceipt
    sampleObservation
    "RequestProject.Cli.Fetch.fetchEntity"
    "receipt:getter:fixture"

_ : getterReceiptCreatesWorldTruth sampleGetterReceipt ≡ false
_ = refl

_ : getterReceiptCreatesSemanticAuthority sampleGetterReceipt ≡ false
_ = refl

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
    "dashi_lean4@349f9b7d"
    reportGenerated
    "csv:mabo-status"
    false
    false
    false

sampleVerificationAttachment : JmdVerificationAbiReceipt
sampleVerificationAttachment =
  mkJmdVerificationAbiReceipt
    sampleVerification
    "RequestProject.Cli.Derive.checkSubChain_sound"
    "receipt:verification:fixture"

_ : verificationReceiptCreatesWorldTruth sampleVerificationAttachment ≡ false
_ = refl

_ : verificationReceiptCreatesAgdaProof sampleVerificationAttachment ≡ false
_ = refl

samplePublicationAttachment : JmdPublicationAbiReceipt
samplePublicationAttachment =
  mkJmdPublicationAbiReceipt
    "csv:mabo-status"
    "RequestProject.Reports.csvOfRows"
    "receipt:publication:fixture"

_ : publicationReceiptCreatesKernelStatus samplePublicationAttachment ≡ false
_ = refl
