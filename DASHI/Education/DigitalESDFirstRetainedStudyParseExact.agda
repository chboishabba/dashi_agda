module DASHI.Education.DigitalESDFirstRetainedStudyParseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDStudyParseInteropExact as Interop
import DASHI.Education.DigitalESDStudyParseExecutionExact as Execution

------------------------------------------------------------------------
-- FIRST REAL RETAINED DIGITAL-ESD STUDY PARSE RECEIPT
--
-- Observed runtime artifact:
--   ERIC:EJ1083370
--
-- Runtime chain:
--
--   retained ERIC source
--      -> PDF retrieval/cache
--      -> pdftotext-layout materialisation
--      -> anchored document nodes
--      -> scholarly parser
--      -> candidate study facets
--
-- This owner records the concrete observed receipt.  The parser/facet layer
-- remains candidate-only and cannot pay study coordinates, create study truth,
-- or create SourceAuditAdmission.
------------------------------------------------------------------------

data StudyFacetRole : Set where
  population
  sample
  intervention
  outcome
  studyDesign
  setting
  timePeriod
  method
  limitation
  funding
  institution
  participantGroup
  measurement
  : StudyFacetRole

record CandidateStudyFacet : Set where
  constructor candidate-study-facet
  field
    facetRole : StudyFacetRole
    matchedTerms : Nat
    evidenceReferenceSummary : String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsStudyTruth : Bool
    createsStudyTruthIsFalse : createsStudyTruth ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open CandidateStudyFacet public

populationFacet : CandidateStudyFacet
populationFacet =
  candidate-study-facet
    population
    33
    "line:190;line:243;line:245;line:406;line:432"
    true refl
    false refl
    false refl

sampleFacet : CandidateStudyFacet
sampleFacet =
  candidate-study-facet
    sample
    1
    "line:599"
    true refl
    false refl
    false refl

interventionFacet : CandidateStudyFacet
interventionFacet =
  candidate-study-facet
    intervention
    26
    "line:117;line:229;line:238;line:370;line:372"
    true refl
    false refl
    false refl

outcomeFacet : CandidateStudyFacet
outcomeFacet =
  candidate-study-facet
    outcome
    78
    "line:82;line:115;line:138;line:170;line:220"
    true refl
    false refl
    false refl

studyDesignFacet : CandidateStudyFacet
studyDesignFacet =
  candidate-study-facet
    studyDesign
    10
    "line:294;line:525;line:608;line:612;line:628"
    true refl
    false refl
    false refl

settingFacet : CandidateStudyFacet
settingFacet =
  candidate-study-facet
    setting
    117
    "line:12;line:15;line:18;line:21;line:45"
    true refl
    false refl
    false refl

timePeriodFacet : CandidateStudyFacet
timePeriodFacet =
  candidate-study-facet
    timePeriod
    3
    "line:483;line:554;line:592"
    true refl
    false refl
    false refl

methodFacet : CandidateStudyFacet
methodFacet =
  candidate-study-facet
    method
    91
    "line:56;line:163;line:171;line:193;line:200"
    true refl
    false refl
    false refl

limitationFacet : CandidateStudyFacet
limitationFacet =
  candidate-study-facet
    limitation
    1
    "line:534"
    true refl
    false refl
    false refl

fundingFacet : CandidateStudyFacet
fundingFacet =
  candidate-study-facet
    funding
    4
    "line:1530;line:1542;line:1552;line:1609"
    true refl
    false refl
    false refl

institutionFacet : CandidateStudyFacet
institutionFacet =
  candidate-study-facet
    institution
    72
    "line:12;line:15;line:18;line:21;line:45"
    true refl
    false refl
    false refl

participantGroupFacet : CandidateStudyFacet
participantGroupFacet =
  candidate-study-facet
    participantGroup
    20
    "line:132;line:157;line:276;line:406;line:408"
    true refl
    false refl
    false refl

measurementFacet : CandidateStudyFacet
measurementFacet =
  candidate-study-facet
    measurement
    125
    "line:112;line:118;line:161;line:221;line:226"
    true refl
    false refl
    false refl

ej1083370CandidateFacets : List CandidateStudyFacet
ej1083370CandidateFacets =
  populationFacet
  ∷ sampleFacet
  ∷ interventionFacet
  ∷ outcomeFacet
  ∷ studyDesignFacet
  ∷ settingFacet
  ∷ timePeriodFacet
  ∷ methodFacet
  ∷ limitationFacet
  ∷ fundingFacet
  ∷ institutionFacet
  ∷ participantGroupFacet
  ∷ measurementFacet
  ∷ []

record FirstRetainedStudyParseReceipt : Set where
  constructor first-retained-study-parse-receipt
  field
    sourceIdentityReference : String
    sourceRevisionReference : String

    sourceArtifactReference : String
    sourceArtifactBytes : Nat
    sourceArtifactSha256 : String

    extractedTextSha256 : String
    extractionEngine : String
    extractionEngineVersion : String

    pageCount : Nat
    extractedCharacterCount : Nat
    documentNodeCount : Nat
    studyFacetCount : Nat

    candidateFacets : List CandidateStudyFacet
    parserSuccess : Bool
    parserSuccessIsTrue : parserSuccess ≡ true

    retainedStudyLane : Bool
    retainedStudyLaneIsTrue : retainedStudyLane ≡ true

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsStudyTruth : Bool
    createsStudyTruthIsFalse : createsStudyTruth ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

    automaticExtractionCoordinatePayment : Bool
    automaticExtractionCoordinatePaymentIsFalse :
      automaticExtractionCoordinatePayment ≡ false

open FirstRetainedStudyParseReceipt public

ej1083370Receipt : FirstRetainedStudyParseReceipt
ej1083370Receipt =
  first-retained-study-parse-receipt
    "ERIC:EJ1083370"
    "fulltext-sha256:f48bad56d0874bb6ed2d109e10ebf495d30534e7e5ce74b8e5800541f6619b89"
    "artifacts/digital-esd/first-reviewed-study/fulltext/cache/ERIC:EJ1083370.pdf"
    931903
    "f48bad56d0874bb6ed2d109e10ebf495d30534e7e5ce74b8e5800541f6619b89"
    "cc248168e15089e8cb76a6ced160afc70e0ff64f74e01cd9140ae03d2eb679e0"
    "pdftotext-layout"
    "pdftotext version 26.08.0"
    30
    110188
    1298
    13
    ej1083370CandidateFacets
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Exact connection to the existing generic study-parse boundaries.
------------------------------------------------------------------------

studyParseInteropBoundary : Interop.StudyParseInteropBoundary
studyParseInteropBoundary = Interop.canonicalStudyParseInteropBoundary

studyParseExecutionBoundary : Execution.StudyParseExecutionBoundary
studyParseExecutionBoundary = Execution.canonicalStudyParseExecutionBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data StudyFacetCandidateCreatesStudyTruth : Set where
data StudyFacetCandidateCreatesSourceAuditAdmission : Set where
data FirstStudyParseCreatesExtractionPayment : Set where
data FirstStudyParseMeansReviewedStudy : Set where
data FirstStudyParseMeansAdmittedStudy : Set where
data MaterialisedTextCreatesClaimTruth : Set where

studyFacetCandidateDoesNotCreateStudyTruth :
  StudyFacetCandidateCreatesStudyTruth → ⊥
studyFacetCandidateDoesNotCreateStudyTruth ()

studyFacetCandidateDoesNotCreateSourceAuditAdmission :
  StudyFacetCandidateCreatesSourceAuditAdmission → ⊥
studyFacetCandidateDoesNotCreateSourceAuditAdmission ()

firstStudyParseDoesNotCreateExtractionPayment :
  FirstStudyParseCreatesExtractionPayment → ⊥
firstStudyParseDoesNotCreateExtractionPayment ()

firstStudyParseDoesNotMeanReviewedStudy :
  FirstStudyParseMeansReviewedStudy → ⊥
firstStudyParseDoesNotMeanReviewedStudy ()

firstStudyParseDoesNotMeanAdmittedStudy :
  FirstStudyParseMeansAdmittedStudy → ⊥
firstStudyParseDoesNotMeanAdmittedStudy ()

materialisedTextDoesNotCreateClaimTruth :
  MaterialisedTextCreatesClaimTruth → ⊥
materialisedTextDoesNotCreateClaimTruth ()

firstRetainedStudyParseReading : String
firstRetainedStudyParseReading =
  "ERIC:EJ1083370 is the first observed retained Digital-ESD study to traverse the concrete full-text parse lane: a 931903-byte PDF with SHA-256 f48bad...6619b89 was materialised by pdftotext-layout into 30 pages / 110188 characters with derived-text SHA-256 cc2481...679e0, then parsed into 1298 anchored document nodes and 13 candidate study-facet families. The receipt is an execution witness for the existing generic StudyParseInterop boundary only. Candidate facets nominate anchored review locations; they do not establish population, sample, intervention, outcomes, design, setting, timing, method, limitations, funding, institution, participant group or measurement as study truth, pay any extraction coordinate, or create SourceAuditAdmission."
