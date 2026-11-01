module DASHI.Cognition.PNF.SensibLawABC730SLRStressRunReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Runtime receipt for the unchanged 9-Sep-2026 ABC 7.30 transcript specimen
-- passed through the normal spaCy -> direct SLR stream.
--
-- The runtime receipt records parser/SLR observations only. It does not promote
-- speaker identity, legal truth, proposition truth, or policy causation.
------------------------------------------------------------------------

record SLRStressRunReceipt : Set where
  constructor slrStressRunReceipt
  field
    sourceBytes : String
    sourceSha256 : String
    paragraphs : String
    sentences : String
    tokens : String
    candidates : String
    residuals : String
    symbols : String
    published : String
    spacyParseNs : String
    slrActiveNs : String
    compilerDiagnostics : Bool
    compilerDiagnosticsIsFalse : compilerDiagnostics ≡ false

canonicalRun : SLRStressRunReceipt
canonicalRun = slrStressRunReceipt
  "18004"
  "44ffc914cde420e597deeb79fc84e1c8d53eef98e338e2901ede587011bab3cc"
  "53"
  "194"
  "3639"
  "819"
  "2820"
  "1133"
  "0"
  "868953206"
  "22916520"
  false refl

------------------------------------------------------------------------
-- High-residual attribution/speaker-boundary observations extracted from the
-- retained parser.tsv and pnf.stdout artifacts.
------------------------------------------------------------------------

record HighResidualSentence : Set where
  constructor highResidualSentence
  field
    sentenceId : String
    residualCount : String
    symbolCount : String
    boundedText : String
    attributionStress : Bool

open HighResidualSentence public

wongHusicBoundarySentence : HighResidualSentence
wongHusicBoundarySentence = highResidualSentence
  "42" "15" "62"
  "Wong unintended-consequences rationale and the following progressive/backbench Palestine-statehood criticism are fused by ASR into one sentence boundary."
  true

thornberryDecisionBasisSentence : HighResidualSentence
thornberryDecisionBasisSentence = highResidualSentence
  "117" "20" "51"
  "Thornberry says she does not know the basis on which Wong made the decision, then attributes a good-faith Palestinian-interest belief to Wong."
  true

thornberryContrastingIsraelViewsSentence : HighResidualSentence
thornberryContrastingIsraelViewsSentence = highResidualSentence
  "110" "18" "59"
  "Long sentence contrasting possible Israeli interpretations of UK action and the political effects of international isolation."
  true

------------------------------------------------------------------------
-- The local cut around the gaslighting exchange is the key speaker-resolution
-- stress fixture. Parser sentence boundaries do not equal broadcast speaker
-- boundaries.
------------------------------------------------------------------------

record BroadcastCutCandidate : Set where
  constructor broadcastCutCandidate
  field
    sentenceId : String
    candidateSpeaker : String
    status : String
    evidenceKind : String
    promotionResidual : String

wongSentence42 : BroadcastCutCandidate
wongSentence42 = broadcastCutCandidate
  "42" "Penny Wong then Ed Husic" "mixed-speaker-boundary"
  "transcript plus same-day public context"
  "recover video/lower-third cut boundary inside parser sentence 42"

husicSentence43 : BroadcastCutCandidate
husicSentence43 = broadcastCutCandidate
  "43" "Ed Husic" "candidate"
  "same-day published quote/context"
  "exact ABC lower-third or clip receipt"

shoebridgeSentence44 : BroadcastCutCandidate
shoebridgeSentence44 = broadcastCutCandidate
  "44" "David Shoebridge" "likely"
  "userWitness"
  "verify with ABC/iView lower-third, exact Greens publication, or equivalent primary receipt"

shoebridgeLeeserSentence45 : BroadcastCutCandidate
shoebridgeLeeserSentence45 = broadcastCutCandidate
  "45" "David Shoebridge then Julian Leeser" "probable-cut-boundary"
  "user witness for first clause; same-day public context for second speaker"
  "recover visual/audio cut point; parser sentence boundary is not sufficient"

leeserSentence46 : BroadcastCutCandidate
leeserSentence46 = broadcastCutCandidate
  "46" "Julian Leeser" "candidate"
  "same-day published quote/context"
  "exact ABC lower-third or clip receipt"

record RuntimeAdmissionBoundary : Set where
  constructor runtimeAdmissionBoundary
  field
    highResidualImpliesWrongSpeaker : Bool
    highResidualImpliesWrongSpeakerIsFalse : highResidualImpliesWrongSpeaker ≡ false
    parserSentenceEqualsSpeakerTurn : Bool
    parserSentenceEqualsSpeakerTurnIsFalse : parserSentenceEqualsSpeakerTurn ≡ false
    likelySpeakerEqualsVerifiedSpeaker : Bool
    likelySpeakerEqualsVerifiedSpeakerIsFalse : likelySpeakerEqualsVerifiedSpeaker ≡ false
    runtimeMayGenerateSpeakerCandidates : Bool
    runtimeMayGenerateSpeakerCandidatesIsTrue : runtimeMayGenerateSpeakerCandidates ≡ true
    runtimeMaySelfPromoteToVerified : Bool
    runtimeMaySelfPromoteToVerifiedIsFalse : runtimeMaySelfPromoteToVerified ≡ false

canonicalRuntimeAdmissionBoundary : RuntimeAdmissionBoundary
canonicalRuntimeAdmissionBoundary = runtimeAdmissionBoundary
  false refl false refl false refl true refl false refl
