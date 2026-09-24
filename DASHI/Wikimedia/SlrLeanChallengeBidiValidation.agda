module DASHI.Wikimedia.SlrLeanChallengeBidiValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact
open import DASHI.Wikimedia.LeanWikidataVerificationExact
open import DASHI.Wikimedia.SlrLeanChallengeBidiExact

sampleObservation : WorldObservation
sampleObservation =
  mkWorldObservation
    "request:counterexample"
    "Q975866"
    "P710"
    "wikidata"
    "wikidata:Q975866:oldid:fixture"
    "sha256:fixture"
    "candidate-value"
    retrievalSucceeded
    currentFreshness
    statedInProvenance

sampleChallenge : SLRLeanChallenge
sampleChallenge =
  slrLeanChallenge
    "challenge:mabo:P710"
    counterexampleCandidate
    "lean:theorem:encoded-relation"
    "Q975866"
    "P710"
    ("wikidata:Q975866:oldid:fixture" ∷ [])
    ("premise:1" ∷ [])
    ("observation:1" ∷ [])
    "alignment:pending"
    true
    false
    false

_ : challengeKind sampleChallenge ≡ counterexampleCandidate
_ = refl

_ : candidateOnly sampleChallenge ≡ true
_ = refl

_ : challengeIsFormalRefutation sampleChallenge ≡ false
_ = refl

sampleResolution : LeanChallengeResolution
sampleResolution =
  leanChallengeResolution
    "resolution:mabo:P710"
    sampleChallenge
    staleImport
    "lean:replay:fixture"
    "source revision changed"
    false
    false
    false

_ : resolutionKind sampleResolution ≡ staleImport
_ = refl

_ : resolutionCreatesWorldTruth sampleResolution ≡ false
_ = refl

_ : resolutionCreatesLegalAuthority sampleResolution ≡ false
_ = refl

wrongObjectResolution : LeanChallengeResolution
wrongObjectResolution =
  leanChallengeResolution
    "resolution:wrong-object"
    sampleChallenge
    wrongObjectResolutionKind
    "lean:replay:wrong-object"
    "attachment target differs"
    false
    false
    false

_ : resolutionKind wrongObjectResolution ≡ wrongObjectResolutionKind
_ = refl

statementTooStrongResolution : LeanChallengeResolution
statementTooStrongResolution =
  leanChallengeResolution
    "resolution:statement-too-strong"
    sampleChallenge
    statementTooStrong
    "lean:replay:too-strong"
    "candidate reproduced outside encoded scope"
    false
    false
    false

_ : resolutionKind statementTooStrongResolution ≡ statementTooStrong
_ = refl
