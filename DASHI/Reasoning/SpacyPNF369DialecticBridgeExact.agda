module DASHI.Reasoning.SpacyPNF369DialecticBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Spacy
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as Evidence
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis
import DASHI.Reasoning.TernarySynthesisLogicQualificationExact as Qualification

------------------------------------------------------------------------
-- EXACT SPACY -> 369 DIALECTIC BRIDGE
--
-- The 369 carrier does not encode dependency labels or manufacture semantic
-- content.  It indexes the review/disposition relation between two actual
-- parser-supported candidate readings and a third synthesis/adjudication
-- coordinate.  The candidates retain their original DependencyWitnesses.
------------------------------------------------------------------------

data CandidateDisposition : Set where
  rejectCandidate
  suspendCandidate
  admitCandidate
  : CandidateDisposition

dispositionTrit : CandidateDisposition → Base.TriTruth
dispositionTrit rejectCandidate = Base.tri-low
dispositionTrit suspendCandidate = Base.tri-mid
dispositionTrit admitCandidate = Base.tri-high

rejectIsNotSuspend :
  dispositionTrit rejectCandidate ≡ dispositionTrit suspendCandidate → ⊥
rejectIsNotSuspend ()

suspendIsNotAdmit :
  dispositionTrit suspendCandidate ≡ dispositionTrit admitCandidate → ⊥
suspendIsNotAdmit ()

------------------------------------------------------------------------
-- One exact dialectic atom retains BOTH parser-supported readings.
--
-- The first two coordinates classify their current review dispositions; the
-- third is a synthesis/adjudication coordinate.  This is exactly the existing
-- 3 x 3 x 3 = 27 carrier, not a new ternary ontology.
------------------------------------------------------------------------

record SpacyCandidateDialectic369Atom : Set₁ where
  constructor spacyCandidateDialectic369Atom
  field
    leftCandidate rightCandidate : Spacy.CandidateSemanticFragment
    leftDisposition rightDisposition : CandidateDisposition
    synthesisDisposition : CandidateDisposition

    chart : Synthesis.SynthesisChoice27
    chartExact :
      chart ≡
      Synthesis.makeSynthesisChoice
        (dispositionTrit leftDisposition)
        (dispositionTrit rightDisposition)
        (dispositionTrit synthesisDisposition)

    comparisonReference : String
    synthesisReference : String

open SpacyCandidateDialectic369Atom public

canonicalChart :
  Spacy.CandidateSemanticFragment →
  Spacy.CandidateSemanticFragment →
  CandidateDisposition → CandidateDisposition → CandidateDisposition →
  Synthesis.SynthesisChoice27
canonicalChart left right leftStatus rightStatus synthesisStatus =
  Synthesis.makeSynthesisChoice
    (dispositionTrit leftStatus)
    (dispositionTrit rightStatus)
    (dispositionTrit synthesisStatus)

makeSpacyCandidateDialectic369Atom :
  (left right : Spacy.CandidateSemanticFragment) →
  (leftStatus rightStatus synthesisStatus : CandidateDisposition) →
  String → String →
  SpacyCandidateDialectic369Atom
makeSpacyCandidateDialectic369Atom left right leftStatus rightStatus synthesisStatus comparisonRef synthesisRef =
  spacyCandidateDialectic369Atom
    left right
    leftStatus rightStatus synthesisStatus
    (canonicalChart left right leftStatus rightStatus synthesisStatus)
    refl
    comparisonRef synthesisRef

parserCandidatesRetained :
  (atom : SpacyCandidateDialectic369Atom) →
  Spacy.DependencyWitness
  × Spacy.DependencyWitness
parserCandidatesRetained atom =
  Spacy.forwardWitness (leftCandidate atom) ,
  Spacy.forwardWitness (rightCandidate atom)

comparisonCoordinatesRetained :
  (left right : Spacy.CandidateSemanticFragment) →
  (leftStatus rightStatus synthesisStatus : CandidateDisposition) →
  Synthesis.comparisonOfSynthesis
    (canonicalChart left right leftStatus rightStatus synthesisStatus)
  ≡
  (dispositionTrit leftStatus , dispositionTrit rightStatus)
comparisonCoordinatesRetained left right leftStatus rightStatus synthesisStatus = refl

synthesisCoordinateRetained :
  (left right : Spacy.CandidateSemanticFragment) →
  (leftStatus rightStatus synthesisStatus : CandidateDisposition) →
  Synthesis.synthesisCoordinate
    (canonicalChart left right leftStatus rightStatus synthesisStatus)
  ≡ dispositionTrit synthesisStatus
synthesisCoordinateRetained left right leftStatus rightStatus synthesisStatus = refl

------------------------------------------------------------------------
-- The parser fibre remains authoritative for candidate membership/resolution.
-- A 369 chart is downstream review geometry; it is not a replacement for the
-- semantic-resolution receipt.
------------------------------------------------------------------------

record ResolvedSpacyPNF369Bridge
    (fibre : Spacy.CandidateSemanticFibre)
    (resolution : Spacy.SemanticResolutionReceipt fibre)
    (assertion : Evidence.PredicateNormalAssertion) : Set₁ where
  constructor resolvedSpacyPNF369Bridge
  field
    dialecticAtom : SpacyCandidateDialectic369Atom
    selectedCandidateIsLeftOrRightReference : String
    pnfCorrespondence :
      Spacy.ResolvedCandidateToEvidencePNF resolution assertion
    reviewReference : String

open ResolvedSpacyPNF369Bridge public

------------------------------------------------------------------------
-- Higher-order logical qualification is retained as ANOTHER coordinate.
-- Tetralemma support and sixfold underdetermination/scope status do not get
-- inferred from the parser dependency or collapsed into tri-mid.
------------------------------------------------------------------------

record SpacyDialecticLogicalQualification
    (atom : SpacyCandidateDialectic369Atom) : Set₁ where
  constructor spacyDialecticLogicalQualification
  field
    qualified : Qualification.SixfoldQualifiedSynthesis
    qualifiedChartMatches :
      Qualification.synthesisCarrier
        (Qualification.tetralemmaQualified qualified)
      ≡ chart atom
    qualificationReference : String

open SpacyDialecticLogicalQualification public

------------------------------------------------------------------------
-- Explicit information boundary.
------------------------------------------------------------------------

record SpacyPNF369DialecticBoundary : Set where
  constructor spacyPNF369DialecticBoundary
  field
    parserCandidateCanCarry369ReviewChart : Bool
    parserCandidateCanCarry369ReviewChartIsTrue :
      parserCandidateCanCarry369ReviewChart ≡ true

    ternaryMidMeansParserFailure : Bool
    ternaryMidMeansParserFailureIsFalse :
      ternaryMidMeansParserFailure ≡ false

    ternaryMidMeansLogicalFalsehood : Bool
    ternaryMidMeansLogicalFalsehoodIsFalse :
      ternaryMidMeansLogicalFalsehood ≡ false

    chartRecoversDependencyWitness : Bool
    chartRecoversDependencyWitnessIsFalse :
      chartRecoversDependencyWitness ≡ false

    chartUniquelyDeterminesSemanticReading : Bool
    chartUniquelyDeterminesSemanticReadingIsFalse :
      chartUniquelyDeterminesSemanticReading ≡ false

    counterpositionEqualsLogicalNegation : Bool
    counterpositionEqualsLogicalNegationIsFalse :
      counterpositionEqualsLogicalNegation ≡ false

    synthesisErasesAlternativeParserReading : Bool
    synthesisErasesAlternativeParserReadingIsFalse :
      synthesisErasesAlternativeParserReading ≡ false

    resolvedPNFBecomesWorldTruth : Bool
    resolvedPNFBecomesWorldTruthIsFalse :
      resolvedPNFBecomesWorldTruth ≡ false

canonicalSpacyPNF369DialecticBoundary : SpacyPNF369DialecticBoundary
canonicalSpacyPNF369DialecticBoundary =
  spacyPNF369DialecticBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
