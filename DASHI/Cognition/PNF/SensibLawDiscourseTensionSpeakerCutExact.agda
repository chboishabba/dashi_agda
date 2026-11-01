module DASHI.Cognition.PNF.SensibLawDiscourseTensionSpeakerCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTranscriptSpeakerResolutionExact as Speaker

------------------------------------------------------------------------
-- Discourse tension is not a lie detector.
--
-- High residual density can be caused by several distinct phenomena:
--   * strategically underspecified language;
--   * source/world-model inconsistency or policy tension;
--   * nested attribution and quotation;
--   * stance discontinuity from an intra-sentence speaker cut;
--   * ASR damage or punctuation loss.
--
-- SLR may use the shape of these signals to propose cut points and competing
-- speaker hypotheses.  None of them independently prove deception or truth.
------------------------------------------------------------------------

data TensionKind : Set where
  semanticUnderspecification : TensionKind
  consequenceValenceUnspecified : TensionKind
  causalMechanismUnspecified : TensionKind
  policyObjectiveActionMismatch : TensionKind
  stanceDiscontinuity : TensionKind
  attributionNesting : TensionKind
  quoteBoundaryUncertain : TensionKind
  asrDisfluency : TensionKind
  sentenceBoundaryOverlap : TensionKind
  worldModelSpeakerMismatch : TensionKind

data TensionDisposition : Set where
  absent : TensionDisposition
  weak : TensionDisposition
  moderate : TensionDisposition
  strong : TensionDisposition

record DiscourseTensionFeature : Set where
  constructor discourseTensionFeature
  field
    sentenceReference : String
    kind : TensionKind
    disposition : TensionDisposition
    evidenceReference : String
    boundedInterpretation : String

open DiscourseTensionFeature public

------------------------------------------------------------------------
-- Cognitive-dissonance-style product.
--
-- "Cognitive dissonance" here means an observable incompatibility or tension
-- among propositions/stances in the discourse model.  It does not assert the
-- private psychological state of any speaker.
------------------------------------------------------------------------

record DiscourseDissonancePacket : Set where
  constructor discourseDissonancePacket
  field
    sentenceReference : String
    semanticTensionPresent : Bool
    transcriptIntegrityRiskPresent : Bool
    likelySpeakerCutPresent : Bool
    deceptionProven : Bool
    explanation : String

open DiscourseDissonancePacket public

------------------------------------------------------------------------
-- ABC 7.30 stress fixture.
------------------------------------------------------------------------

wongUnintendedConsequencesUnderspecified : DiscourseTensionFeature
wongUnintendedConsequencesUnderspecified = discourseTensionFeature
  "spaCy sentence 42 / ABC730 C029"
  semanticUnderspecification
  strong
  "uploaded parser.tsv + ABC transcript C029"
  "Affected classes are named but the concrete consequence, sign, probability and mechanism are not specified in the transcript surface."

wongPalestinianValenceUnspecified : DiscourseTensionFeature
wongPalestinianValenceUnspecified = discourseTensionFeature
  "spaCy sentence 42 / ABC730 C029"
  consequenceValenceUnspecified
  strong
  "ABC730 C029"
  "The phrase 'unintended consequences for Palestinians' does not state whether the anticipated Palestinian consequence is harmful, beneficial or mixed."

wongMechanismUnspecified : DiscourseTensionFeature
wongMechanismUnspecified = discourseTensionFeature
  "spaCy sentence 42 / ABC730 C029"
  causalMechanismUnspecified
  strong
  "ABC730 C029; Ferguson/Thornberry follow-up"
  "The recovered public rationale does not identify a causal mechanism by which the proposed settlement-economic restriction would adversely affect Palestinians."

wongPolicyMismatch : DiscourseTensionFeature
wongPolicyMismatch = discourseTensionFeature
  "ABC730 C029-C032 and C040-C042"
  policyObjectiveActionMismatch
  strong
  "Australian government states settlement expansion threatens Palestinian statehood while declining the broader UK-style settlement measure"
  "This is a source-backed policy-tension coordinate suitable for analysis; it does not independently prove bad faith."

sentence42Overlap : DiscourseTensionFeature
sentence42Overlap = discourseTensionFeature
  "spaCy sentence 42"
  sentenceBoundaryOverlap
  strong
  "uploaded parser.tsv / speaker fixture C029-C030"
  "The parser sentence contains Wong's rationale and then the beginning of a different progressive/backbench stance, indicating that sentence segmentation crosses a likely broadcast speaker cut."

sentence45StanceCut : DiscourseTensionFeature
sentence45StanceCut = discourseTensionFeature
  "spaCy sentence 45"
  stanceDiscontinuity
  strong
  "uploaded parser.tsv / speaker fixture C032-C033"
  "The sentence transitions from 'unbelievable gaslighting from Labor' to uncertainty that sanctions advance a two-state solution, a sharp stance reversal compatible with a Shoebridge-to-Leeser broadcast cut."

sentence45SpeakerMismatch : DiscourseTensionFeature
sentence45SpeakerMismatch = discourseTensionFeature
  "spaCy sentence 45"
  worldModelSpeakerMismatch
  strong
  "current speaker candidates: David Shoebridge likely for C032; Julian Leeser candidate for C033"
  "One-speaker attribution across the whole sentence conflicts with the current discourse/world-model candidate sequence."

canonicalWongDissonance : DiscourseDissonancePacket
canonicalWongDissonance = discourseDissonancePacket
  "spaCy sentence 42"
  true
  true
  true
  false
  "Semantic underspecification and policy tension coincide with a parser boundary that likely spans Wong into another speaker. This combination raises inspection priority but proves neither deception nor speaker identity."

canonicalGaslightingCutDissonance : DiscourseDissonancePacket
canonicalGaslightingCutDissonance = discourseDissonancePacket
  "spaCy sentence 45"
  true
  true
  true
  false
  "A strong stance discontinuity plus current speaker-world-model incompatibility makes an intra-sentence cut the preferred transcript-integrity hypothesis."

------------------------------------------------------------------------
-- Cut proposal contract.
------------------------------------------------------------------------

data CutEvidenceKind : Set where
  punctuationWeakness : CutEvidenceKind
  stanceFlip : CutEvidenceKind
  firstPersonPerspectiveShift : CutEvidenceKind
  partyPositionShift : CutEvidenceKind
  attributionVerbBoundary : CutEvidenceKind
  residualDensitySpike : CutEvidenceKind
  worldModelSpeakerShift : CutEvidenceKind
  visualCutEvidence : CutEvidenceKind

record IntraSentenceCutProposal : Set where
  constructor intraSentenceCutProposal
  field
    sentenceReference : String
    leftSpeaker : Speaker.SpeakerCandidate
    rightSpeaker : Speaker.SpeakerCandidate
    cutAnchor : String
    evidenceKind : CutEvidenceKind
    candidateOnly : Bool
    promotionResidual : String

open IntraSentenceCutProposal public

sentence42WongToHusic : IntraSentenceCutProposal
sentence42WongToHusic = intraSentenceCutProposal
  "spaCy sentence 42"
  Speaker.pennyWong
  Speaker.edHusic
  "after 'for Israelis' / before 'we can't say we're for the state of Palestine'"
  stanceFlip
  true
  "confirm exact video edit/lower-third or source-aligned timing"

sentence45ShoebridgeToLeeser : IntraSentenceCutProposal
sentence45ShoebridgeToLeeser = intraSentenceCutProposal
  "spaCy sentence 45"
  Speaker.davidShoebridge
  Speaker.julianLeeser
  "after 'unbelievable gaslighting from Labor' / before two-state-solution sanctions-effectiveness response"
  worldModelSpeakerShift
  true
  "confirm exact video edit/lower-third; Shoebridge remains likely from user witness and Leeser remains candidate until exact ABC cut is recovered"

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

record DissonanceAdmissionBoundary : Set where
  constructor dissonanceAdmissionBoundary
  field
    highResidualProvesWeaseliness : Bool
    highResidualProvesWeaselinessIsFalse : highResidualProvesWeaseliness ≡ false
    semanticTensionProvesDeception : Bool
    semanticTensionProvesDeceptionIsFalse : semanticTensionProvesDeception ≡ false
    stanceFlipMayProposeSpeakerCut : Bool
    stanceFlipMayProposeSpeakerCutIsTrue : stanceFlipMayProposeSpeakerCut ≡ true
    worldModelMismatchMayRaiseCutPriority : Bool
    worldModelMismatchMayRaiseCutPriorityIsTrue : worldModelMismatchMayRaiseCutPriority ≡ true
    proposedCutSelfVerifiesSpeakerIdentity : Bool
    proposedCutSelfVerifiesSpeakerIdentityIsFalse : proposedCutSelfVerifiesSpeakerIdentity ≡ false

canonicalDissonanceAdmissionBoundary : DissonanceAdmissionBoundary
canonicalDissonanceAdmissionBoundary = dissonanceAdmissionBoundary false refl false refl true refl true refl false refl
