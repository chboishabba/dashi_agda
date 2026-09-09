module DASHI.Cognition.PNF.SensibLawTranscriptBoundaryFibreClassifierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Transcript-boundary interpretation after deterministic v2 cut scoring.
--
-- The cut scorer observes local structural discontinuity.  This owner keeps
-- the interpretation of that discontinuity in a candidate fibre rather than
-- collapsing it to speaker-change / no-speaker-change.
------------------------------------------------------------------------

data BoundaryFibreKind : Set where
  speakerCut : BoundaryFibreKind
  reporterQuoteHandoff : BoundaryFibreKind
  attributionNesting : BoundaryFibreKind
  asrDamage : BoundaryFibreKind
  rhetoricalPivot : BoundaryFibreKind

record BoundaryFibreScore : Set where
  constructor boundaryFibreScore
  field
    kind : BoundaryFibreKind
    score : String
    evidenceReference : String
    candidateOnly : Bool

open BoundaryFibreScore public

record BoundaryFibreVector : Set where
  constructor boundaryFibreVector
  field
    sourceSha256 : String
    sentenceReference : String
    splitReference : String
    v2CutReceiptReference : String
    speaker : BoundaryFibreScore
    quoteHandoff : BoundaryFibreScore
    nesting : BoundaryFibreScore
    asr : BoundaryFibreScore
    rhetorical : BoundaryFibreScore
    topCandidate : BoundaryFibreKind
    classifierSchema : String

open BoundaryFibreVector public

------------------------------------------------------------------------
-- Empirical signatures from the transcript-wide ABC 7.30 run.
------------------------------------------------------------------------

record FibreSignature : Set where
  constructor fibreSignature
  field
    kind : BoundaryFibreKind
    boundedSignature : String
    downstreamTreatment : String

speakerSignature : FibreSignature
speakerSignature = fibreSignature speakerCut
  "cross-profile or perspective shift + independent discourse cue + low content dependency crossing"
  "propose new top-level discourse agent; do not promote speaker identity without source receipt"

quoteSignature : FibreSignature
quoteSignature = fibreSignature reporterQuoteHandoff
  "reporting/framing clause followed by first-person or quoted proposition, often near attribution/reporting vocabulary"
  "create subordinate quoted discourse frame attached to reporter/source carrier"

nestingSignature : FibreSignature
nestingSignature = fibreSignature attributionNesting
  "epistemic/source predicate such as according to, said, concluded, argues, believes, reported"
  "retain speaker container and lift proposition into source/modal wrapper"

asrSignature : FibreSignature
asrSignature = fibreSignature asrDamage
  "broken phrase, repeated token sequence, sentence-fragment seam, anomalous dependency severance or transcription disfluency"
  "emit transcript-repair candidate before semantic admission"

rhetoricalSignature : FibreSignature
rhetoricalSignature = fibreSignature rhetoricalPivot
  "adversative/concessive marker inside otherwise stable speaker/profile context"
  "preserve speaker container and attach contrast/concession relation"

------------------------------------------------------------------------
-- Runtime/admission boundary.
------------------------------------------------------------------------

record FibreClassifierBoundary : Set where
  constructor fibreClassifierBoundary
  field
    v2CutScoreProvesSpeakerChange : Bool
    v2CutScoreProvesSpeakerChangeIsFalse : v2CutScoreProvesSpeakerChange ≡ false
    topFibreScoreIsAdjudicatedTruth : Bool
    topFibreScoreIsAdjudicatedTruthIsFalse : topFibreScoreIsAdjudicatedTruth ≡ false
    fibreScoresMayCompete : Bool
    fibreScoresMayCompeteIsTrue : fibreScoresMayCompete ≡ true
    asrCandidateMayTriggerRepairPass : Bool
    asrCandidateMayTriggerRepairPassIsTrue : asrCandidateMayTriggerRepairPass ≡ true
    speakerCandidateMayFeedPNFAttribution : Bool
    speakerCandidateMayFeedPNFAttributionIsTrue : speakerCandidateMayFeedPNFAttribution ≡ true
    runtimeMaySelfVerifySpeaker : Bool
    runtimeMaySelfVerifySpeakerIsFalse : runtimeMaySelfVerifySpeaker ≡ false

canonicalFibreClassifierBoundary : FibreClassifierBoundary
canonicalFibreClassifierBoundary = fibreClassifierBoundary
  false refl false refl true refl true refl true refl false refl

------------------------------------------------------------------------
-- Empirical regression coordinates from transcript-wide v2 run.
------------------------------------------------------------------------

sentence45ExpectedFamily : String
sentence45ExpectedFamily =
  "sentence 45 split 7 should retain speakerCut among top fibres; Shoebridge remains likely/user-witness and Leeser candidate until exact source promotion"

sentence117ExpectedFamily : String
sentence117ExpectedFamily =
  "sentence 117 adversative but-pivot should prefer rhetoricalPivot over speakerCut despite high v2 cut score"

sentence118ExpectedFamily : String
sentence118ExpectedFamily =
  "sentence 118 according-to-Penny-Wong region should prefer attributionNesting over speakerCut"

sentence42ExpectedFamily : String
sentence42ExpectedFamily =
  "sentence 42 split 35 should keep reporterQuoteHandoff/speakerCut both live until broadcast/source boundary evidence distinguishes narrator-to-quote from direct audio splice"
