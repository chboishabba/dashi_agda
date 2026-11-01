module DASHI.Interop.SLRRuntimeValidationHandoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Runtime validation handoff, 2026-09-11.
--
-- The handoff archive separates three kinds of evidence:
--   * ABC730: actual SLR -> SensibLaw CandidateWorldModel normalization parity;
--   * GWB: full retained/projected text SLR execution + direct/reference parity;
--   * AU: broad retained-source diagnostic streaming, not legal/world semantics.
-- Brexit remains outside the language benchmark because only a structured
-- intent fixture is retained, not a narrative/source-text specimen.
------------------------------------------------------------------------

data ValidationClass : Set where
  candidateWorldNormalizationParity : ValidationClass
  fullCorpusExecutionParity : ValidationClass
  retainedSourceDiagnosticStream : ValidationClass
  unavailableNarrativeBenchmark : ValidationClass

record RuntimeValidationReceipt : Set where
  constructor runtimeValidationReceipt
  field
    validationReference : String
    validationClass : ValidationClass
    documentCount : Nat
    sentenceCount : Nat
    paragraphCount : Nat
    parityFailureCount : Nat
    publicationCount : Nat
    parserRelativeRatioReference : String
    sourceProjectionReference : String
    candidateWorldClaimCount : Nat
    candidateWorldRelationCount : Nat
    candidateWorldConflictCount : Nat
    candidateWorldResidualCount : Nat
    normalizationDrift : Bool
    semanticPromotion : Bool
    notes : String

open RuntimeValidationReceipt public

abc730CandidateWorldParity : RuntimeValidationReceipt
abc730CandidateWorldParity = runtimeValidationReceipt
  "slr-validation-handoff-20260911/abc730-parity"
  candidateWorldNormalizationParity
  1 0 0 0 0
  "not a performance corpus receipt"
  "source hash + SLR span/quality/role tables"
  405 53 76 153
  false false
  "SensibLaw normalize_world_model preserved the SLR CandidateWorldModel collections with normalization_drift=false."

gwbFullExecutionParity : RuntimeValidationReceipt
gwbFullExecutionParity = runtimeValidationReceipt
  "slr-validation-handoff-20260911/gwb-full-certification.json"
  fullCorpusExecutionParity
  10 41134 12742 0 0
  "1.0530460427706279"
  "10-source projected-text manifest; 4,072,448 projected bytes"
  0 0 0 0
  false false
  "Full GWB run: direct/reference parity checked for every sentence, no publication, architectural parser-relative gate passed."

auRetainedSourceStream : RuntimeValidationReceipt
auRetainedSourceStream = runtimeValidationReceipt
  "slr-validation-handoff-20260911/au-retained-source-stream.json"
  retainedSourceDiagnosticStream
  45 19235 14029 0 0
  "1.0337013044011951"
  "legal_principles_au_v1/raw + follow/raw supported retained sources"
  0 0 0 0
  false false
  "Diagnostic streaming only: execution/parity/source-accounting receipt, not legal or world-model semantic certification."

brexitNarrativeBenchmark : RuntimeValidationReceipt
brexitNarrativeBenchmark = runtimeValidationReceipt
  "ITIR structured brexit_intent_record.json only"
  unavailableNarrativeBenchmark
  0 0 0 0 0
  "not-run"
  "no retained Brexit narrative/source text"
  0 0 0 0
  false false
  "Serialising the structured intent fixture as prose would not constitute a source-text/discourse benchmark."

validationReceipts : List RuntimeValidationReceipt
validationReceipts =
  abc730CandidateWorldParity ∷
  gwbFullExecutionParity ∷
  auRetainedSourceStream ∷
  brexitNarrativeBenchmark ∷ []

archiveSha256 : String
archiveSha256 = "f7d2a59bb9370162aaea1b9b369175a6dc41533d4fd1580443b9f9bf84754910"

------------------------------------------------------------------------
-- What these receipts pay, and what they do not.
------------------------------------------------------------------------

record SLRValidationBoundary : Set where
  constructor slrValidationBoundary
  field
    sensibLawCarrierParityPaid : Bool
    crossCorpusExecutionParityPaid : Bool
    broadRetainedSourceStreamingPaid : Bool
    goldSpeakerBoundaryBenchmarkPaid : Bool
    worldConstraintSemanticsPaid : Bool
    canonicalClaimIdentityProjectionPaid : Bool
    legalSemanticCertificationPaidByAUDiagnostic : Bool
    brexitDiscourseBenchmarkPaid : Bool

canonicalSLRValidationBoundary : SLRValidationBoundary
canonicalSLRValidationBoundary =
  slrValidationBoundary
    true true true
    false false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CarrierParityMeansSemanticIdentity : Set where
data ZeroParityFailuresMeansWorldTruth : Set where
data DiagnosticLegalStreamMeansLegalCertification : Set where
data PerformanceGateMeansClaimCorrectness : Set where
data StructuredFixtureMeansNarrativeBenchmark : Set where

carrierParityDoesNotMeanSemanticIdentity : CarrierParityMeansSemanticIdentity → ⊥
carrierParityDoesNotMeanSemanticIdentity ()

zeroParityFailuresDoNotMeanWorldTruth : ZeroParityFailuresMeansWorldTruth → ⊥
zeroParityFailuresDoNotMeanWorldTruth ()

diagnosticStreamDoesNotMeanLegalCertification :
  DiagnosticLegalStreamMeansLegalCertification → ⊥
diagnosticStreamDoesNotMeanLegalCertification ()

performanceDoesNotMeanClaimCorrectness : PerformanceGateMeansClaimCorrectness → ⊥
performanceDoesNotMeanClaimCorrectness ()

structuredFixtureDoesNotMeanNarrativeBenchmark :
  StructuredFixtureMeansNarrativeBenchmark → ⊥
structuredFixtureDoesNotMeanNarrativeBenchmark ()
