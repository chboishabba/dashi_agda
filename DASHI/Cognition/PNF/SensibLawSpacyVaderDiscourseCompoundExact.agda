module DASHI.Cognition.PNF.SensibLawSpacyVaderDiscourseCompoundExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Cognition.PNF.SensibLawDeterministicSentimentProducerExact as Sentiment
import DASHI.Cognition.PNF.SensibLawDiscourseTensionSpeakerCutExact as Tension
import DASHI.Cognition.PNF.SensibLawTranscriptSpeakerResolutionExact as Speaker
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as NegScope

------------------------------------------------------------------------
-- Compound observer: parser structure + lexicon valence + discourse tension.
--
-- No component is semantic authority.  The useful signal is the relation
-- among orthogonal observations: e.g. affectively bland wording can coexist
-- with high underspecification/policy tension; a sharp valence/stance change
-- can increase the priority of an intra-sentence speaker-cut hypothesis.
------------------------------------------------------------------------

data CompoundFeatureKind : Set where
  parserDependencyShape : CompoundFeatureKind
  parserNegationScopeResidual : CompoundFeatureKind
  parserCoordinationScopeResidual : CompoundFeatureKind
  attributionDepth : CompoundFeatureKind
  modalHedgeDensity : CompoundFeatureKind
  agentOmission : CompoundFeatureKind
  sentimentValence : CompoundFeatureKind
  sentimentDiscontinuity : CompoundFeatureKind
  structuralResidualDensity : CompoundFeatureKind
  affectiveNeutralStructuralTension : CompoundFeatureKind
  speakerCutPriority : CompoundFeatureKind

data ObservationStatus : Set where
  retained : ObservationStatus
  runtimePending : ObservationStatus
  candidateOnly : ObservationStatus

record CompoundObservation : Set where
  constructor compoundObservation
  field
    sourceSpanReference : String
    featureKind : CompoundFeatureKind
    status : ObservationStatus
    producerReference : String
    evidenceReference : String
    boundedInterpretation : String

open CompoundObservation public

------------------------------------------------------------------------
-- Existing spaCy projection is reused, not duplicated.
------------------------------------------------------------------------

spacyObservationOwner : String
spacyObservationOwner =
  "DASHI.Cognition.PNF.SpacyNumericProjection.SpacyTokenObservation"

negationScopeOwner : String
negationScopeOwner =
  "DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact"

parserIsObservationNotAuthority : Bool
parserIsObservationNotAuthority = false

------------------------------------------------------------------------
-- ABC 7.30 compounds.
------------------------------------------------------------------------

wongStructuralUnderspecification : CompoundObservation
wongStructuralUnderspecification = compoundObservation
  "spaCy sentence 42 / ABC730 C029"
  structuralResidualDensity
  retained
  "SLR residual stream + discourse-tension owner"
  "15 residuals observed for the sentence containing the unintended-consequences rationale and the following speaker material"
  "High residual density coincides with both semantic underspecification and a likely speaker-boundary crossing; it does not choose between those explanations by itself."

wongVaderPending : CompoundObservation
wongVaderPending = compoundObservation
  "ABC730 C029 exact Wong span only"
  sentimentValence
  runtimePending
  "DASHI.Cognition.PNF.SensibLawDeterministicSentimentProducerExact.vaderParityReceipt"
  "score exact isolated Wong span with pinned vader_parity producer"
  "No sentiment score is predeclared. The purpose is to test whether affective neutrality coexists with strong structural/policy tension."

wongNeutralTensionHypothesis : CompoundObservation
wongNeutralTensionHypothesis = compoundObservation
  "ABC730 C029 exact Wong span only"
  affectiveNeutralStructuralTension
  candidateOnly
  "compound observer"
  "requires VADER receipt + existing underspecification features"
  "Candidate compound: relatively neutral lexical sentiment together with strong omission/underspecification and policy-objective tension. This is an interpretable discourse feature, not evidence of deception."

sentence45ValenceCutPending : CompoundObservation
sentence45ValenceCutPending = compoundObservation
  "spaCy sentence 45 / ABC730 C032-C033"
  sentimentDiscontinuity
  runtimePending
  "vader_parity on left/right cut hypotheses"
  "score likely-Shoebridge left span and candidate-Leeser right span independently"
  "A material left/right valence difference may support a speaker-cut priority signal when combined with stance and world-model discontinuity; absence of such a difference does not refute the cut."

sentence45CutPriorityCompound : CompoundObservation
sentence45CutPriorityCompound = compoundObservation
  "spaCy sentence 45 / ABC730 C032-C033"
  speakerCutPriority
  candidateOnly
  "Tension.sentence45ShoebridgeToLeeser + sentiment discontinuity runtime"
  "stance flip + world-model speaker shift already present; sentiment is an auxiliary feature"
  "Prefer a multi-feature cut proposal over any single sentiment or residual threshold."

------------------------------------------------------------------------
-- Reproducible feature bundle contract.
------------------------------------------------------------------------

record ReproducibleDiscourseFeatureBundle : Set where
  constructor reproducibleDiscourseFeatureBundle
  field
    sourceSha256 : String
    parserProducerVersion : String
    parserModelDigest : String
    sentimentProducerVersion : String
    sentimentLexiconDigest : String
    featureSchemaVersion : String
    sentenceReference : String
    parserFeatureReference : String
    sentimentFeatureReference : String
    tensionFeatureReference : String
    speakerHypothesisReference : String

open ReproducibleDiscourseFeatureBundle public

abcRunBundlePending : ReproducibleDiscourseFeatureBundle
abcRunBundlePending = reproducibleDiscourseFeatureBundle
  "44ffc914...011bab3cc"
  "spaCy runtime used for uploaded parser.tsv; exact package/model version still to be captured from environment lock/receipt"
  "pending exact installed en_core_web_sm wheel/model digest"
  "vader_parity 0.1.0"
  "pending vendored VADER/emoji lexicon digest from runtime/build receipt"
  "slr-discourse-compound-v1"
  "spaCy sentences 42 and 45"
  "uploaded parser.tsv / pnf.stdout"
  "pending vader runtime fixture"
  "SensibLawDiscourseTensionSpeakerCutExact"
  "SensibLawTranscriptSpeakerResolutionExact"

------------------------------------------------------------------------
-- Hard non-collapse boundaries.
------------------------------------------------------------------------

record CompoundAdmissionBoundary : Set where
  constructor compoundAdmissionBoundary
  field
    sentimentScoreIsTruthScore : Bool
    sentimentScoreIsTruthScoreIsFalse : sentimentScoreIsTruthScore ≡ false
    neutralPlusResidualProvesWeaseliness : Bool
    neutralPlusResidualProvesWeaselinessIsFalse : neutralPlusResidualProvesWeaseliness ≡ false
    parserModelOutputIsSemanticAuthority : Bool
    parserModelOutputIsSemanticAuthorityIsFalse : parserModelOutputIsSemanticAuthority ≡ false
    compoundMayRankInspectionPriority : Bool
    compoundMayRankInspectionPriorityIsTrue : compoundMayRankInspectionPriority ≡ true
    compoundMayProposeSpeakerCut : Bool
    compoundMayProposeSpeakerCutIsTrue : compoundMayProposeSpeakerCut ≡ true
    compoundSelfVerifiesSpeakerOrTruth : Bool
    compoundSelfVerifiesSpeakerOrTruthIsFalse : compoundSelfVerifiesSpeakerOrTruth ≡ false

canonicalCompoundAdmissionBoundary : CompoundAdmissionBoundary
canonicalCompoundAdmissionBoundary = compoundAdmissionBoundary false refl false refl false refl true refl true refl false refl
