module DASHI.Cognition.PNF.SensibLawMaboBrennanDawsonIssueResidualLiveExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboPrimaryTextParserBatchMaterialisedExact as Batch
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SpacyExecutableSemanticRuleBankExact as RuleBank
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact as Issue

------------------------------------------------------------------------
-- LIVE MABO SAME-ISSUE ALIGNMENT
--
-- Parser structure proposes clause candidates.  Reviewed source metadata says
-- which judge authored each passage.  A separate reviewed issue-alignment
-- receipt is required before Brennan and Dawson can be compared on one issue.
-- The contrast is not encoded as Boolean negation.
------------------------------------------------------------------------

brennanContentAdmission :
  RuleBank.ShapeAdmission Batch.brennanStateContentWitness Candidate.clausalComplement
brennanContentAdmission = RuleBank.shapeAdmission refl
  "primary-text-v0.1 Brennan ccomp shape admission"
  "spaCy ccomp(state, rejects)"

brennanContentCandidate : Candidate.CandidateSemanticFragment
brennanContentCandidate = RuleBank.clausalComplementRule
  Batch.brennanStateContentWitness brennanContentAdmission
  "event:mabo:brennan:state" "event:mabo:brennan:reject-notion"

brennanNegationCandidate : Candidate.CandidateSemanticFragment
brennanNegationCandidate = Candidate.negationCandidate
  Batch.brennanNegationWitness
  "event:mabo:brennan:extinguish-native-title"

brennanTitleObjectCandidate : Candidate.CandidateSemanticFragment
brennanTitleObjectCandidate = Candidate.objectCandidate
  Batch.brennanExtinguishObjectWitness
  "event:mabo:brennan:extinguish-native-title"
  "native-title"

dawsonContentAdmission :
  RuleBank.ShapeAdmission Batch.dawsonModalContentWitness Candidate.clausalComplement
dawsonContentAdmission = RuleBank.shapeAdmission refl
  "primary-text-v0.1 Dawson ccomp shape admission"
  "spaCy ccomp(think, be)"

dawsonContentCandidate : Candidate.CandidateSemanticFragment
dawsonContentCandidate = RuleBank.clausalComplementRule
  Batch.dawsonModalContentWitness dawsonContentAdmission
  "event:mabo:dawson:think" "event:mabo:dawson:must-be"

dawsonViewpointCandidate : Candidate.CandidateSemanticFragment
dawsonViewpointCandidate = Candidate.subjectCandidate
  Batch.dawsonViewpointSubjectWitness
  "event:mabo:dawson:think" "speaker:mabo:dawson-j"

------------------------------------------------------------------------
-- Reviewed judicial proposition receipts.
-- These summaries are review-layer proposition identifiers over bounded source
-- passages; they are not produced by spaCy and do not claim final holding or
-- world truth.
------------------------------------------------------------------------

record ReviewedJudicialProposition : Set where
  constructor reviewedJudicialProposition
  field
    propositionReference : String
    speakerReference : String
    sourcePassageReference : String
    sourceHash : String
    parserCandidate : Candidate.CandidateSemanticFragment
    propositionSummary : String
    propositionStatus : Status.PropositionStatus
    truthStatus : Status.TruthStatus
    reviewedSourceAttribution : Bool
    reviewedSourceAttributionIsTrue : reviewedSourceAttribution ≡ true
    parserAloneSelectedSpeaker : Bool
    parserAloneSelectedSpeakerIsFalse : parserAloneSelectedSpeaker ≡ false
    parserAloneProvesHolding : Bool
    parserAloneProvesHoldingIsFalse : parserAloneProvesHolding ≡ false
open ReviewedJudicialProposition public

brennanSurvivalProposition : ReviewedJudicialProposition
brennanSurvivalProposition = reviewedJudicialProposition
  "proposition:mabo:brennan:antecedent-native-rights-survive-sovereignty"
  "judge:Mabo-No2:Brennan-J"
  (Batch.sourcePassage Batch.brennanSpecimen)
  (Batch.fixtureSha256 Batch.brennanSpecimen)
  brennanContentCandidate
  "reviewed bounded passage: Brennan J states that Australian common law rejects automatic absolute beneficial Crown ownership on sovereignty and accepts survival of antecedent indigenous rights and interests"
  Status.represented Status.truthUnresolved
  true refl false refl false refl

dawsonRecognitionProposition : ReviewedJudicialProposition
dawsonRecognitionProposition = reviewedJudicialProposition
  "proposition:mabo:dawson:crown-recognition-may-be-inferred-from-facts"
  "judge:Mabo-No2:Dawson-J"
  (Batch.sourcePassage Batch.dawsonSpecimen)
  (Batch.fixtureSha256 Batch.dawsonSpecimen)
  dawsonContentCandidate
  "reviewed bounded passage: Dawson J treats Crown recognition of native interests as potentially inferential from all the facts, including acquiescence and continued undisturbed occupation/use"
  Status.represented Status.truthUnresolved
  true refl false refl false refl

maboRecognitionIssue : Issue.LegalIssue
maboRecognitionIssue = Issue.legalIssue
  "issue:mabo:no2:native-title-recognition-across-sovereignty"
  "issue-proposition:mabo:native-interests-recognition-survival-after-sovereignty"
  "proceeding:Mabo-v-Queensland-No2-1992-HCA23"
  "legal-system:Australia-common-law:source-resolution-separate"

record ReviewedSameIssueAlignment
    (left right : ReviewedJudicialProposition) : Set where
  constructor reviewedSameIssueAlignment
  field
    issue : Issue.LegalIssue
    leftPropositionReference : String
    leftReferenceExact : leftPropositionReference ≡ propositionReference left
    rightPropositionReference : String
    rightReferenceExact : rightPropositionReference ≡ propositionReference right
    sameIssueReviewed : Bool
    sameIssueReviewedIsTrue : sameIssueReviewed ≡ true
    alignmentReferences : List String
    parserAloneAuthorizesAlignment : Bool
    parserAloneAuthorizesAlignmentIsFalse : parserAloneAuthorizesAlignment ≡ false
open ReviewedSameIssueAlignment public

brennanDawsonSameIssue :
  ReviewedSameIssueAlignment brennanSurvivalProposition dawsonRecognitionProposition
brennanDawsonSameIssue = reviewedSameIssueAlignment
  maboRecognitionIssue
  (propositionReference brennanSurvivalProposition) refl
  (propositionReference dawsonRecognitionProposition) refl
  true refl
  ( "Mabo (No 2), Brennan J paragraphs 61-62" ∷
    "Mabo (No 2), Dawson J paragraphs 13-14" ∷
    "reviewed alignment: both passages bear on recognition/survival of native interests across acquisition/change of sovereignty" ∷ [])
  false refl

------------------------------------------------------------------------
-- Typed contrast: not Boolean negation.
------------------------------------------------------------------------

data MaboContrastKind : Set where
  recognitionBasisContrast
  legalCharacterisationContrast
  evidentialInferenceContrast
  : MaboContrastKind

record MaboControversyResidual : Set where
  constructor maboControversyResidual
  field
    alignment : ReviewedSameIssueAlignment brennanSurvivalProposition dawsonRecognitionProposition
    primaryKind : MaboContrastKind
    secondaryKind : MaboContrastKind
    unresolvedQuestion : String
    residualReference : String
    finalAdjudicationClaimed : Bool
    finalAdjudicationClaimedIsFalse : finalAdjudicationClaimed ≡ false
open MaboControversyResidual public

brennanDawsonResidual : MaboControversyResidual
brennanDawsonResidual = maboControversyResidual
  brennanDawsonSameIssue
  recognitionBasisContrast
  legalCharacterisationContrast
  "How do the Brennan and Dawson passages differ in the legal basis by which native interests survive, are recognized, or are inferred across a change/acquisition of sovereignty?"
  "primary-text-v0.1 reviewed same-issue contrast; not an assertion that the two passages are logical negations"
  false refl

------------------------------------------------------------------------
-- Reverse obligation inspired by the Lee/Justice proof-search lane.
------------------------------------------------------------------------

data MaboResidualObligation : Set where
  inspectRecognitionBasis
  inspectAuthorityChain
  inspectTemporalSovereigntyRelation
  inspectFullReasonsBeforeAdjudication
  : MaboResidualObligation

data MaboDiscriminator : Set where
  recognitionRuleDiscriminator
  authorityChainDiscriminator
  chronologyDiscriminator
  fullReasonsDiscriminator
  : MaboDiscriminator

data MaboWorkKind : Set where
  thinkWork lookWork testWork : MaboWorkKind

record CompiledMaboResidualSearch : Set where
  constructor compiledMaboResidualSearch
  field
    residual : MaboControversyResidual
    obligation : MaboResidualObligation
    discriminator : MaboDiscriminator
    workKind : MaboWorkKind
    targetSourceQuery : String
    compilationReference : String
open CompiledMaboResidualSearch public

compileMaboResidualSearch : MaboControversyResidual → CompiledMaboResidualSearch
compileMaboResidualSearch residual = compiledMaboResidualSearch
  residual
  inspectRecognitionBasis
  recognitionRuleDiscriminator
  lookWork
  "retrieve the surrounding Brennan and Dawson reasons and cited authorities bearing on Crown recognition, survival, inference and sovereignty"
  "same-issue residual -> recognition-basis obligation -> targeted source inspection"

brennanDawsonSearch : CompiledMaboResidualSearch
brennanDawsonSearch = compileMaboResidualSearch brennanDawsonResidual

searchTargetsRecognitionBasis :
  obligation brennanDawsonSearch ≡ inspectRecognitionBasis
searchTargetsRecognitionBasis = refl

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data SameIssueMeansLogicalNegation : Set where
data ParserCandidateCreatesJudicialHolding : Set where
data ReviewedSpeakerMetadataMakesWorldTruth : Set where
data BrennanPropositionIsDawsonNegation : Set where
\data BoundedContrastCompletesMaboAdjudication : Set where

sameIssueDoesNotMeanLogicalNegation : SameIssueMeansLogicalNegation → ⊥
sameIssueDoesNotMeanLogicalNegation ()
parserCandidateDoesNotCreateHolding : ParserCandidateCreatesJudicialHolding → ⊥
parserCandidateDoesNotCreateHolding ()
reviewedSpeakerDoesNotMakeWorldTruth : ReviewedSpeakerMetadataMakesWorldTruth → ⊥
reviewedSpeakerDoesNotMakeWorldTruth ()
brennanIsNotEncodedAsDawsonBooleanNegation : BrennanPropositionIsDawsonNegation → ⊥
brennanIsNotEncodedAsDawsonBooleanNegation ()
boundedContrastDoesNotCompleteAdjudication : BoundedContrastCompletesMaboAdjudication → ⊥
boundedContrastDoesNotCompleteAdjudication ()

record MaboPrimaryTextResidualBoundary : Set where
  constructor maboPrimaryTextResidualBoundary
  field
    parserStructureCandidateOnly : Bool
    sourceAttributionReviewedSeparately : Bool
    sameIssueAlignmentReviewedSeparately : Bool
    contrastIsBooleanNegation : Bool
    truthResolvedByParser : Bool
    targetedResidualSearchOwned : Bool

canonicalMaboPrimaryTextResidualBoundary : MaboPrimaryTextResidualBoundary
canonicalMaboPrimaryTextResidualBoundary =
  maboPrimaryTextResidualBoundary true true true false false true
