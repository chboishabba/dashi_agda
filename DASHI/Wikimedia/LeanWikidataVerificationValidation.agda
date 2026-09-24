module DASHI.Wikimedia.LeanWikidataVerificationValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact
open import DASHI.Wikimedia.LeanWikidataVerificationExact

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
    staleFreshness
    statedInProvenance

encodedPassedStale : LeanVerificationReceipt
encodedPassedStale =
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

_ : encodingStatus encodedPassedStale ≡ encoded
_ = refl

_ : freshnessStatus (verificationObservation encodedPassedStale) ≡ staleFreshness
_ = refl

_ : kernelStatus encodedPassedStale ≡ checkPassed
_ = refl

_ : objectAlignment encodedPassedStale ≡ exactSameObject
_ = refl

currentNotRun : LeanVerificationReceipt
currentNotRun =
  leanVerificationReceipt
    (mkWorldObservation
      "request:Q1501525:P710:current"
      "Q1501525"
      "P710"
      "wikidata"
      "wikidata:Q1501525:current"
      "sha256:current"
      "Q975866"
      retrievalSucceeded
      currentFreshness
      referenceURLProvenance)
    encoded
    importNotChecked
    checkNotRun
    checkNotRun
    sameObjectDifferentRepresentation
    relationUnresolved
    "lean:query:not-run"
    "jmd-aristotle:lean4-v4.28.0"
    reportNotGenerated
    ""
    false
    false
    false

_ : kernelStatus currentNotRun ≡ checkNotRun
_ = refl

kernelPassedWrongObject : LeanVerificationReceipt
kernelPassedWrongObject =
  leanVerificationReceipt
    sampleObservation
    encoded
    importFaithfullyRepresented
    checkPassed
    checkPassed
    wrongObject
    relationAligned
    "lean:theorem:fixture"
    "jmd-aristotle:lean4-v4.28.0"
    reportGenerated
    "csv:fixture"
    false
    false
    false

_ : kernelStatus kernelPassedWrongObject ≡ checkPassed
_ = refl

_ : objectAlignment kernelPassedWrongObject ≡ wrongObject
_ = refl

_ : verificationCreatesWorldTruth kernelPassedWrongObject ≡ false
_ = refl

_ : verificationCreatesLegalAuthority kernelPassedWrongObject ≡ false
_ = refl

sampleProofDebtStatus : RelationProofDebtStatus
sampleProofDebtStatus =
  relationProofDebtStatus
    "status:mabo:P710"
    mathematicalEncoded
    exactStatementKnown
    leanKernelPassed
    staleFreshness
    exactAttachment
    csvGenerated

_ : mathematicalStatus sampleProofDebtStatus ≡ mathematicalEncoded
_ = refl

_ : statementStatus sampleProofDebtStatus ≡ exactStatementKnown
_ = refl

_ : certificationStatus sampleProofDebtStatus ≡ leanKernelPassed
_ = refl

_ : proofDebtFreshnessStatus sampleProofDebtStatus ≡ staleFreshness
_ = refl

_ : attachmentStatus sampleProofDebtStatus ≡ exactAttachment
_ = refl

_ : proofDebtPublicationStatus sampleProofDebtStatus ≡ csvGenerated
_ = refl
