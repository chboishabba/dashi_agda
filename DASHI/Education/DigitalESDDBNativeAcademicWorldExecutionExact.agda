module DASHI.Education.DigitalESDDBNativeAcademicWorldExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDCandidateWorldExecutionExact as World
import DASHI.Education.DigitalESDStudyParseInteropExact as Parse
import DASHI.Education.DigitalESDAcademicCorpusWorldCrossPollinationExact as Academic

------------------------------------------------------------------------
-- DB-NATIVE ACADEMIC WORLD EXECUTION
--
-- Runtime owners:
--   dashi_agda:
--     interop_scripts/digital_esd/run_world.py
--
--   SLR:
--     sensiblaw-world-expansion-runtime / digital_esd_world
--
-- Production state lives in PostgreSQL.  Runtime lowering reuses the exact
-- nineteen-coordinate manuscript extraction vocabulary.  PNF/source evidence
-- may nominate a coordinate for review; nomination does not pay the coordinate
-- and lack of a nomination does not establish absence.
--
-- Study-family hypotheses are likewise candidate genealogy only.  They may
-- schedule review but do not establish duplicate-publication identity,
-- same-empirical-study identity, evidence independence or claim truth.
------------------------------------------------------------------------

candidateWorldBoundary : World.DigitalESDCandidateWorldExecutionBoundary
candidateWorldBoundary = World.canonicalDigitalESDCandidateWorldExecutionBoundary

academicWorldBoundary : Academic.DigitalESDAcademicCorpusWorldBoundary
academicWorldBoundary = Academic.canonicalDigitalESDAcademicCorpusWorldBoundary

extractionCoordinateCount : Nat
extractionCoordinateCount = Parse.baseExtractionCoordinateCount

effectiveExtractionCoordinateCount : Nat
effectiveExtractionCoordinateCount = Parse.effectiveExtractionCoordinateCount

record DBNativeCoordinateNominationBoundary : Set where
  constructor db-native-coordinate-nomination-boundary
  field
    existingNineteenCoordinateSchemaReused : Bool
    existingNineteenCoordinateSchemaReusedIsTrue :
      existingNineteenCoordinateSchemaReused ≡ true

    exactSourceRevisionRetained : Bool
    exactSourceRevisionRetainedIsTrue :
      exactSourceRevisionRetained ≡ true

    exactStatementAndSpanRetained : Bool
    exactStatementAndSpanRetainedIsTrue :
      exactStatementAndSpanRetained ≡ true

    pnfBatchReferenceRetained : Bool
    pnfBatchReferenceRetainedIsTrue :
      pnfBatchReferenceRetained ≡ true

    nominationRequiresPositiveEvidence : Bool
    nominationRequiresPositiveEvidenceIsTrue :
      nominationRequiresPositiveEvidence ≡ true

    parserNominationPaysCoordinate : Bool
    parserNominationPaysCoordinateIsFalse :
      parserNominationPaysCoordinate ≡ false

    missingNominationCreatesAbsenceFinding : Bool
    missingNominationCreatesAbsenceFindingIsFalse :
      missingNominationCreatesAbsenceFinding ≡ false

    nominationCreatesSemanticAuthority : Bool
    nominationCreatesSemanticAuthorityIsFalse :
      nominationCreatesSemanticAuthority ≡ false

    nominationCreatesClaimTruth : Bool
    nominationCreatesClaimTruthIsFalse :
      nominationCreatesClaimTruth ≡ false

open DBNativeCoordinateNominationBoundary public

canonicalDBNativeCoordinateNominationBoundary :
  DBNativeCoordinateNominationBoundary
canonicalDBNativeCoordinateNominationBoundary =
  db-native-coordinate-nomination-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

record DBNativeAcademicGenealogyBoundary : Set where
  constructor db-native-academic-genealogy-boundary
  field
    studyFamilyHypothesesPersisted : Bool
    studyFamilyHypothesesPersistedIsTrue :
      studyFamilyHypothesesPersisted ≡ true

    genealogyRequiresReview : Bool
    genealogyRequiresReviewIsTrue :
      genealogyRequiresReview ≡ true

    genealogyCreatesDuplicateDecision : Bool
    genealogyCreatesDuplicateDecisionIsFalse :
      genealogyCreatesDuplicateDecision ≡ false

    genealogyCreatesSameEmpiricalStudyIdentity : Bool
    genealogyCreatesSameEmpiricalStudyIdentityIsFalse :
      genealogyCreatesSameEmpiricalStudyIdentity ≡ false

    genealogyCreatesEvidenceIndependence : Bool
    genealogyCreatesEvidenceIndependenceIsFalse :
      genealogyCreatesEvidenceIndependence ≡ false

    genealogyCreatesSemanticAuthority : Bool
    genealogyCreatesSemanticAuthorityIsFalse :
      genealogyCreatesSemanticAuthority ≡ false

    genealogyCreatesClaimTruth : Bool
    genealogyCreatesClaimTruthIsFalse :
      genealogyCreatesClaimTruth ≡ false

open DBNativeAcademicGenealogyBoundary public

canonicalDBNativeAcademicGenealogyBoundary :
  DBNativeAcademicGenealogyBoundary
canonicalDBNativeAcademicGenealogyBoundary =
  db-native-academic-genealogy-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

data ParserNominationPaysExtractionCoordinate : Set where
data MissingNominationCreatesAbsenceFact : Set where
data GenealogyHypothesisCreatesDuplicateDecision : Set where
data GenealogyHypothesisCreatesSameEmpiricalStudy : Set where
data GenealogyHypothesisCreatesEvidenceIndependence : Set where
data CandidateWorldJsonBecomesRuntimeDatabase : Set where

parserNominationDoesNotPayExtractionCoordinate :
  ParserNominationPaysExtractionCoordinate → ⊥
parserNominationDoesNotPayExtractionCoordinate ()

missingNominationDoesNotCreateAbsenceFact :
  MissingNominationCreatesAbsenceFact → ⊥
missingNominationDoesNotCreateAbsenceFact ()

genealogyHypothesisDoesNotCreateDuplicateDecision :
  GenealogyHypothesisCreatesDuplicateDecision → ⊥
genealogyHypothesisDoesNotCreateDuplicateDecision ()

genealogyHypothesisDoesNotCreateSameEmpiricalStudy :
  GenealogyHypothesisCreatesSameEmpiricalStudy → ⊥
genealogyHypothesisDoesNotCreateSameEmpiricalStudy ()

genealogyHypothesisDoesNotCreateEvidenceIndependence :
  GenealogyHypothesisCreatesEvidenceIndependence → ⊥
genealogyHypothesisDoesNotCreateEvidenceIndependence ()

candidateWorldJsonDoesNotBecomeRuntimeDatabase :
  CandidateWorldJsonBecomesRuntimeDatabase → ⊥
candidateWorldJsonDoesNotBecomeRuntimeDatabase ()

dbNativeAcademicWorldExecutionReading : String
dbNativeAcademicWorldExecutionReading =
  "Digital-ESD world execution is PostgreSQL-native. Verified/materialised retained texts enter the existing SCALE-1 source-revision, exact-region, parser-job, Statement/PNF and reconciliation spine. Runtime study-coordinate nominations use the existing nineteen-coordinate manuscript extraction vocabulary and retain exact source-revision, statement, span and PNF-batch provenance; a nomination is review-only, pays no coordinate, and missing nomination is not an absence fact. Persisted study-family hypotheses remain candidate genealogy: they schedule review but create neither duplicate/same-study identity nor evidence independence. The agent receives bounded inspection projections rather than a corpus-wide JSON graph."
