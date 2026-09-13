module DASHI.Interop.TiRCorderSpokenIntentGrammarRuddCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Interop.TiRCorderVoiceEditInteroceptionAntiPanopticonExact as Voice

------------------------------------------------------------------------
-- TIRCORDER SPOKEN-INTENT GRAMMAR x TAVIS RUDD VOICE-CODING PRECEDENT
--
-- Source precedent retained here:
--   Tavis Rudd, "Using Python to Code by Voice", PyCon US 2013,
--   video published 21 March 2013.
--   https://www.youtube.com/watch?v=8SkdfdXWYaI
--
-- The source is used as architectural precedent for a user-extensible mapping
-- from utterances to actions, context-sensitive grammars, and chained commands.
-- It is not treated as proof that a modern TiRCorder interpretation is correct,
-- optimal, ergonomic, safe, or semantically equivalent to Rudd's system.
------------------------------------------------------------------------

record VoiceGrammarSourceReceipt : Set where
  constructor voiceGrammarSourceReceipt
  field
    author : String
    title : String
    publicationYear : Nat
    canonicalUrl : String
    relationship : String

open VoiceGrammarSourceReceipt public

rudd2013 : VoiceGrammarSourceReceipt
rudd2013 =
  voiceGrammarSourceReceipt
    "Tavis Rudd"
    "Using Python to Code by Voice"
    2013
    "https://www.youtube.com/watch?v=8SkdfdXWYaI"
    "architectural precedent for explicit utterance-to-action grammars and chained spoken commands"

------------------------------------------------------------------------
-- 1. Recognition, interpretation, admission and execution remain distinct.
------------------------------------------------------------------------

data GrammarMatchStatus : Set where
  noGrammarMatch : GrammarMatchStatus
  candidateGrammarMatch : GrammarMatchStatus
  exactGrammarMatch : GrammarMatchStatus

record SpokenIntentContext : Set where
  constructor spokenIntentContext
  field
    sourceSpanReference : String
    recentTargetReference : String
    selectionReference : String
    commandModeEnabled : Bool
    inlineCommandsEnabled : Bool

open SpokenIntentContext public

record SpokenIntentCandidate : Set where
  constructor spokenIntentCandidate
  field
    recognizedUtteranceReference : String
    proposedFibre : Voice.SpokenIntentFibre
    proposedEditKind : Voice.VoiceEditKind
    grammarMatch : GrammarMatchStatus
    grammarRuleReference : String
    targetReference : String
    replacementReference : String
    candidateScore : Nat
    executableUnderPolicy : Bool
    rationaleReference : String

open SpokenIntentCandidate public

------------------------------------------------------------------------
-- 2. Pinned deterministic grammar classes.
------------------------------------------------------------------------

data DeterministicGrammarClass : Set where
  exactFormattingPhrase : DeterministicGrammarClass
  exactPunctuationPhrase : DeterministicGrammarClass
  correctionMarkerWithReplacement : DeterministicGrammarClass
  deleteRecentPhrase : DeterministicGrammarClass
  selectionFormatPhrase : DeterministicGrammarClass
  literalDocumentContent : DeterministicGrammarClass
  unresolvedAmbiguousMarker : DeterministicGrammarClass

record DeterministicGrammarRule : Set where
  constructor deterministicGrammarRule
  field
    ruleId : String
    utterancePatternReference : String
    grammarClass : DeterministicGrammarClass
    outputFibre : Voice.SpokenIntentFibre
    outputEditKind : Voice.VoiceEditKind
    requiresRecentTarget : Bool
    requiresSelection : Bool
    requiresCommandPermission : Bool

open DeterministicGrammarRule public

newParagraphRule : DeterministicGrammarRule
newParagraphRule =
  deterministicGrammarRule
    "voice-intent-v1:new-paragraph"
    "new paragraph | paragraph break"
    exactFormattingPhrase
    Voice.formattingCommand
    Voice.paragraphBreak
    false
    false
    true

actuallyReplacementRule : DeterministicGrammarRule
actuallyReplacementRule =
  deterministicGrammarRule
    "voice-intent-v1:actually-replacement"
    "actually <replacement>"
    correctionMarkerWithReplacement
    Voice.selfCorrection
    Voice.replaceRecent
    true
    false
    true

------------------------------------------------------------------------
-- 3. Candidate fibre discipline.
--
-- A recognized token can be perfectly accurate while being offered to the
-- wrong consumer.  "actually" is the canonical example: correction marker,
-- ordinary discourse marker, quote content and ASR artefact are distinct
-- interpretations.
------------------------------------------------------------------------

data ExactRecognitionDeterminesIntent : Set where
exactRecognitionDoesNotDetermineIntent : ExactRecognitionDeterminesIntent → ⊥
exactRecognitionDoesNotDetermineIntent ()

data GrammarMatchDeterminesSpeakerMeaning : Set where
grammarMatchDoesNotDetermineSpeakerMeaning : GrammarMatchDeterminesSpeakerMeaning → ⊥
grammarMatchDoesNotDetermineSpeakerMeaning ()

data ActuallyAlwaysMeansCorrection : Set where
actuallyDoesNotAlwaysMeanCorrection : ActuallyAlwaysMeansCorrection → ⊥
actuallyDoesNotAlwaysMeanCorrection ()

data CommandPhraseMayRewriteVerbatim : Set where
commandPhraseMayNotRewriteVerbatim : CommandPhraseMayRewriteVerbatim → ⊥
commandPhraseMayNotRewriteVerbatim ()

------------------------------------------------------------------------
-- 4. Fail-closed admission.
------------------------------------------------------------------------

data SpokenEditAdmission : SpokenIntentCandidate → Set where
  admitDeterministicCommand :
    {candidate : SpokenIntentCandidate} →
    executableUnderPolicy candidate ≡ true →
    SpokenEditAdmission candidate

record AmbiguousCandidateSet : Set where
  constructor ambiguousCandidateSet
  field
    sourceUtteranceReference : String
    candidateCount : Nat
    candidatesReference : String
    retainedWithoutAutomaticExecution : Bool

open AmbiguousCandidateSet public

unresolvedCandidateMustRemainNonExecuting :
  {candidate : SpokenIntentCandidate} →
  proposedFibre candidate ≡ Voice.unresolvedIntent →
  executableUnderPolicy candidate ≡ false →
  Bool
unresolvedCandidateMustRemainNonExecuting _ _ = true

------------------------------------------------------------------------
-- 5. Continuous/chained command composition.
--
-- Rudd explicitly described commands as chainable into continuous speech.
-- TiRCorder adopts the compositional idea, but each segment retains provenance
-- and admission independently so one valid command cannot authorize its
-- neighbours by association.
------------------------------------------------------------------------

record SpokenCommandSegment : Set where
  constructor spokenCommandSegment
  field
    segmentIndex : Nat
    sourceSpanReference : String
    candidateReference : String
    admitted : Bool

open SpokenCommandSegment public

record ChainedSpokenCommandReceipt : Set where
  constructor chainedSpokenCommandReceipt
  field
    utteranceReference : String
    segmentationReference : String
    segmentCount : Nat
    segmentReceiptsReference : String
    longestMatchPolicyReference : String
    deterministicReplayReference : String

open ChainedSpokenCommandReceipt public

data OneAdmittedSegmentAdmitsWholeChain : Set where
oneAdmittedSegmentDoesNotAdmitWholeChain : OneAdmittedSegmentAdmitsWholeChain → ⊥
oneAdmittedSegmentDoesNotAdmitWholeChain ()

------------------------------------------------------------------------
-- 6. Cross-pollination with the existing verbatim/edit/rendered boundary.
------------------------------------------------------------------------

record SpokenIntentInterpreterBoundary : Set where
  constructor spokenIntentInterpreterBoundary
  field
    recognitionSeparatedFromIntent : Bool
    intentSeparatedFromAdmission : Bool
    admissionSeparatedFromExecution : Bool
    grammarIsPinnedAndDeterministic : Bool
    ordinaryContentRemainsCandidate : Bool
    ambiguousMarkersRemainRetainable : Bool
    commandModeIsIndependentPermission : Bool
    recentTargetRequiredForRelativeCorrection : Bool
    chainedCommandsAreSegmentProvenanced : Bool
    verbatimCarrierRemainsImmutable : Bool
    sourcePrecedentCreatesSemanticAuthority : Bool

canonicalSpokenIntentInterpreterBoundary : SpokenIntentInterpreterBoundary
canonicalSpokenIntentInterpreterBoundary =
  spokenIntentInterpreterBoundary
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false

voiceEditBoundaryAnchor : Voice.TiRCorderVoiceEditInteroceptionBoundary
voiceEditBoundaryAnchor = Voice.canonicalTiRCorderVoiceEditInteroceptionBoundary
