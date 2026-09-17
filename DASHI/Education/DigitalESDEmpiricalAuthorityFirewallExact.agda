module DASHI.Education.DigitalESDEmpiricalAuthorityFirewallExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling

------------------------------------------------------------------------
-- DIGITAL-ESD EMPIRICAL AUTHORITY FIREWALL
--
-- A review may have perfectly reproducible formal processing while still
-- carrying an unsupported premise, a mistaken extraction, or an over-broad
-- source interpretation.  Provenance, reproducibility, empirical support and
-- epistemic correctness therefore remain independently payable obligations.
------------------------------------------------------------------------

data EvidenceLayer : Set where
  sourceAttributed : EvidenceLayer
  sourceClaimTranscribed : EvidenceLayer
  extractionReproduced : EvidenceLayer
  formalConsequenceDerived : EvidenceLayer
  empiricalSupportPaid : EvidenceLayer
  claimCeilingAdmitted : EvidenceLayer

data FormalEntailmentDeterminesEmpiricalGrounding : Set where
data ProceduralReproducibilityDeterminesExtractionCorrectness : Set where
data AttributionCompletenessDeterminesClaimSupport : Set where
data ContentHashDeterminesClaimTruth : Set where
data SourceDiscussionDeterminesAdmittedClaimCeiling : Set where
data StableExportDeterminesSearchCompleteness : Set where

formalEntailmentDoesNotDetermineEmpiricalGrounding :
  FormalEntailmentDeterminesEmpiricalGrounding → ⊥
formalEntailmentDoesNotDetermineEmpiricalGrounding ()

proceduralReproducibilityDoesNotDetermineExtractionCorrectness :
  ProceduralReproducibilityDeterminesExtractionCorrectness → ⊥
proceduralReproducibilityDoesNotDetermineExtractionCorrectness ()

attributionCompletenessDoesNotDetermineClaimSupport :
  AttributionCompletenessDeterminesClaimSupport → ⊥
attributionCompletenessDoesNotDetermineClaimSupport ()

contentHashDoesNotDetermineClaimTruth : ContentHashDeterminesClaimTruth → ⊥
contentHashDoesNotDetermineClaimTruth ()

sourceDiscussionDoesNotDetermineAdmittedClaimCeiling :
  SourceDiscussionDeterminesAdmittedClaimCeiling → ⊥
sourceDiscussionDoesNotDetermineAdmittedClaimCeiling ()

stableExportDoesNotDetermineSearchCompleteness :
  StableExportDeterminesSearchCompleteness → ⊥
stableExportDoesNotDetermineSearchCompleteness ()

------------------------------------------------------------------------
-- Constructive collision: identical formal consequence, different grounding.
------------------------------------------------------------------------

data GroundingWorld : Set where
  derivedFromExternallyPaidPremise : GroundingWorld
  derivedFromTranscribedPremiseOnly : GroundingWorld

data EntailmentSurface : Set where
  sameFormalConsequence : EntailmentSurface

data GroundingQuery : Set where
  groundingQuestion : GroundingQuery

data GroundingAnswer : Set where
  groundedAnswer : GroundingAnswer
  ungroundedAnswer : GroundingAnswer

formalSurface : GroundingWorld → EntailmentSurface
formalSurface derivedFromExternallyPaidPremise = sameFormalConsequence
formalSurface derivedFromTranscribedPremiseOnly = sameFormalConsequence

GroundingAnswerFor : GroundingQuery → Set
GroundingAnswerFor groundingQuestion = GroundingAnswer

askGrounding : (query : GroundingQuery) → GroundingWorld → GroundingAnswerFor query
askGrounding groundingQuestion derivedFromExternallyPaidPremise = groundedAnswer
askGrounding groundingQuestion derivedFromTranscribedPremiseOnly = ungroundedAnswer

groundingQuestions : Query.InquiryQuestionFamily GroundingWorld GroundingQuery
groundingQuestions = Query.inquiryQuestionFamily GroundingAnswerFor askGrounding

formalSurfaceDoesNotFactorGrounding :
  Query.FactorsThrough groundingQuestions formalSurface groundingQuestion → ⊥
formalSurfaceDoesNotFactorGrounding factor = answer-collision
  where
    collision : groundedAnswer ≡ ungroundedAnswer
    collision =
      trans
        (Query.factorisation factor derivedFromExternallyPaidPremise)
        (sym (Query.factorisation factor derivedFromTranscribedPremiseOnly))

    answer-collision : ⊥
    answer-collision with () ← collision

------------------------------------------------------------------------
-- Constructive collision: same reproducible extraction procedure, different
-- extraction correctness.
------------------------------------------------------------------------

data ExtractionWorld : Set where
  reproducibleCorrectExtraction : ExtractionWorld
  reproducibleWrongExtraction : ExtractionWorld

data ReproducibilitySurface : Set where
  sameReproducibleProcedure : ReproducibilitySurface

data ExtractionQuery : Set where
  extractionCorrectnessQuestion : ExtractionQuery

data ExtractionAnswer : Set where
  extractionCorrect : ExtractionAnswer
  extractionIncorrect : ExtractionAnswer

reproducibilitySurface : ExtractionWorld → ReproducibilitySurface
reproducibilitySurface reproducibleCorrectExtraction = sameReproducibleProcedure
reproducibilitySurface reproducibleWrongExtraction = sameReproducibleProcedure

ExtractionAnswerFor : ExtractionQuery → Set
ExtractionAnswerFor extractionCorrectnessQuestion = ExtractionAnswer

askExtraction : (query : ExtractionQuery) → ExtractionWorld → ExtractionAnswerFor query
askExtraction extractionCorrectnessQuestion reproducibleCorrectExtraction = extractionCorrect
askExtraction extractionCorrectnessQuestion reproducibleWrongExtraction = extractionIncorrect

extractionQuestions : Query.InquiryQuestionFamily ExtractionWorld ExtractionQuery
extractionQuestions = Query.inquiryQuestionFamily ExtractionAnswerFor askExtraction

reproducibilityDoesNotFactorExtractionCorrectness :
  Query.FactorsThrough extractionQuestions reproducibilitySurface extractionCorrectnessQuestion → ⊥
reproducibilityDoesNotFactorExtractionCorrectness factor = answer-collision
  where
    collision : extractionCorrect ≡ extractionIncorrect
    collision =
      trans
        (Query.factorisation factor reproducibleCorrectExtraction)
        (sym (Query.factorisation factor reproducibleWrongExtraction))

    answer-collision : ⊥
    answer-collision with () ← collision

------------------------------------------------------------------------
-- Existing authority surfaces retained.
------------------------------------------------------------------------

attributedSourceCoreReceipt = Attr.canonicalAttributedSourceCoreReceipt
studyClaimCeilingBoundary : Ceiling.StudyClaimCeilingBoundary
studyClaimCeilingBoundary = Ceiling.canonicalStudyClaimCeilingBoundary

record EmpiricalAuthorityBoundary : Set where
  constructor empiricalAuthorityBoundary
  field
    attributionRetained : Bool
    attributionRetainedIsTrue : attributionRetained ≡ true
    reproducibilityRetained : Bool
    reproducibilityRetainedIsTrue : reproducibilityRetained ≡ true
    empiricalGroundingSeparate : Bool
    empiricalGroundingSeparateIsTrue : empiricalGroundingSeparate ≡ true
    extractionCorrectnessSeparate : Bool
    extractionCorrectnessSeparateIsTrue : extractionCorrectnessSeparate ≡ true
    claimCeilingRemainsIndependent : Bool
    claimCeilingRemainsIndependentIsTrue : claimCeilingRemainsIndependent ≡ true
    formalProcessingCreatesEmpiricalAuthority : Bool
    formalProcessingCreatesEmpiricalAuthorityIsFalse :
      formalProcessingCreatesEmpiricalAuthority ≡ false
    stableHashCreatesClaimTruth : Bool
    stableHashCreatesClaimTruthIsFalse : stableHashCreatesClaimTruth ≡ false
    stableExportCreatesSearchCompleteness : Bool
    stableExportCreatesSearchCompletenessIsFalse :
      stableExportCreatesSearchCompleteness ≡ false

open EmpiricalAuthorityBoundary public

canonicalEmpiricalAuthorityBoundary : EmpiricalAuthorityBoundary
canonicalEmpiricalAuthorityBoundary =
  empiricalAuthorityBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

empiricalAuthorityReading : String
empiricalAuthorityReading =
  "Digital-ESD source attribution, deterministic extraction, content hashes, reproducible scripts and formal entailment establish provenance or procedural invariance only. They do not by themselves establish extraction correctness, empirical grounding, claim truth, search completeness or an admitted study-claim ceiling. Those obligations remain independently payable against the exact source and consumer question."
