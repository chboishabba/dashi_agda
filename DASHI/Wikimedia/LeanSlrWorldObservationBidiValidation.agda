module DASHI.Wikimedia.LeanSlrWorldObservationBidiValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact

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

sampleLeanGetter : LeanGetterObservation
sampleLeanGetter =
  mkLeanGetterObservation
    sampleObservation
    "jmd-aristotle:lean-getter"

sampleSlrGetter : SlrGetterObservation
sampleSlrGetter =
  mkSlrGetterObservation
    sampleObservation
    "slr:wikidata-getter"

_ : requestReference (normalizeLeanGetter sampleLeanGetter) ≡ "request:Q1501525:P710"
_ = refl

_ : objectReference (normalizeLeanGetter sampleLeanGetter) ≡ "Q1501525"
_ = refl

_ : relationReference (normalizeSlrGetter sampleSlrGetter) ≡ "P710"
_ = refl

_ : sourceRevisionReference (normalizeSlrGetter sampleSlrGetter) ≡
    "wikidata:Q1501525:oldid:2333409615"
_ = refl

_ : contentDigestReference (normalizeLeanGetter sampleLeanGetter) ≡ "sha256:fixture"
_ = refl

_ : getterCreatesSemanticAuthority sampleLeanGetter ≡ false
_ = refl

_ : slrGetterCreatesClaimTruth sampleSlrGetter ≡ false
_ = refl

sampleParityResidual : GetterParityResidual
sampleParityResidual =
  getterParityResidual
    "getter-parity:mabo:P710"
    sampleLeanGetter
    sampleSlrGetter
    valueMismatch
    false
    false

_ : mismatchKind sampleParityResidual ≡ valueMismatch
_ = refl

_ : disagreementChoosesWorldTruth sampleParityResidual ≡ false
_ = refl
