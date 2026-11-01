module DASHI.Empirical.GRQuantumBenchmarkProtocol where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_)

import DASHI.Unified.GRQuantumFiniteDiagnosticReceipt as Diagnostic

------------------------------------------------------------------------
-- Matched-quality numerical comparison.
--
-- The protocol follows the existing flagship receipt validator: held-out data,
-- an explicit baseline, matched quality, runtime, memory, side-information, and
-- leakage controls are mandatory.  Resource comparisons without matched quality
-- are not accepted.

data BenchmarkDomain : Set where
  weakFieldGR : BenchmarkDomain
  strongFieldGR : BenchmarkDomain
  freeQuantumDynamics : BenchmarkDomain
  qftCorrelation : BenchmarkDomain
  jointSemiclassicalBackreaction : BenchmarkDomain

record SolverIdentity : Set where
  constructor solver-identity
  field
    name : String
    version : String
    sourceRevision : String
    configurationHash : String
    hardware : String
    numericPrecision : String
    deterministicSeedPolicy : String
open SolverIdentity public

record DatasetSplit : Set where
  constructor dataset-split
  field
    datasetIdentifier : String
    datasetRevision : String
    trainingCases : Nat
    calibrationCases : Nat
    heldOutCases : Nat
    splitManifestHash : String
    leakageAuditReference : String
open DatasetSplit public

record ResourceMeasurement : Set where
  constructor resource-measurement
  field
    wallTimeNanoseconds : Nat
    peakMemoryBytes : Nat
    energyMicrojoules : Nat
    warmupPolicy : String
    repetitionCount : Nat
    aggregationMethod : String
open ResourceMeasurement public

record MatchedQualityBenchmark (domain : BenchmarkDomain) : Set₁ where
  field
    Input : Set
    CandidateOutput : Set
    ReferenceOutput : Set
    QualityValue : Set

    candidateSolver : SolverIdentity
    referenceSolver : SolverIdentity
    dataset : DatasetSplit

    candidateRun : Input → CandidateOutput
    referenceRun : Input → ReferenceOutput
    candidateQuality : CandidateOutput → QualityValue
    referenceQuality : ReferenceOutput → QualityValue

    QualityTolerance : Set
    matchedQuality :
      (input : Input) →
      CandidateOutput → ReferenceOutput → QualityTolerance → Set
    tolerance : QualityTolerance
    matchedQualityProof :
      (input : Input) →
      matchedQuality input (candidateRun input) (referenceRun input) tolerance

    candidateResources : Input → ResourceMeasurement
    referenceResources : Input → ResourceMeasurement

    sideInformationAccounted : Set
    sideInformationAccountedProof : sideInformationAccounted
    heldOutEvaluation : Set
    heldOutEvaluationProof : heldOutEvaluation
    noTestLeakage : Set
    noTestLeakageProof : noTestLeakage
    numericalErrorBudgetClosed : Set
    numericalErrorBudgetClosedProof : numericalErrorBudgetClosed
    reproducibleArtifact : Set
    reproducibleArtifactProof : reproducibleArtifact
    independentRerun : Set
    independentRerunProof : independentRerun

    artifactManifest : List String
open MatchedQualityBenchmark public

record GRQuantumBenchmarkSuite : Set₁ where
  field
    weakField : MatchedQualityBenchmark weakFieldGR
    strongField : MatchedQualityBenchmark strongFieldGR
    quantumDynamics : MatchedQualityBenchmark freeQuantumDynamics
    qftCorrelator : MatchedQualityBenchmark qftCorrelation
    semiclassicalBackreaction :
      MatchedQualityBenchmark jointSemiclassicalBackreaction

    sameObservableDefinitionsAsCalibration : Set
    sameObservableDefinitionsAsCalibrationProof :
      sameObservableDefinitionsAsCalibration
    uncertaintyIntervalsReported : Set
    uncertaintyIntervalsReportedProof : uncertaintyIntervalsReported
    failedCasesRetained : Set
    failedCasesRetainedProof : failedCasesRetained
    benchmarkProtocolFrozenBeforeHeldOutRun : Set
    benchmarkProtocolFrozenBeforeHeldOutRunProof :
      benchmarkProtocolFrozenBeforeHeldOutRun
open GRQuantumBenchmarkSuite public

------------------------------------------------------------------------
-- Existing finite diagnostic and reusable benchmark-governance references.

record ExistingBenchmarkReferences : Set where
  constructor existing-benchmark-references
  field
    finiteDiagnostic : Diagnostic.GRQuantumFiniteDiagnosticReceipt
    finiteDiagnosticScript : String
    flagshipValidator : String
    calibrationPattern : String
    validationGovernancePattern : String
    scope : String
open ExistingBenchmarkReferences public

canonicalExistingBenchmarkReferences : ExistingBenchmarkReferences
canonicalExistingBenchmarkReferences =
  existing-benchmark-references
    Diagnostic.canonicalGRQuantumFiniteDiagnosticReceipt
    "scripts/run_gr_quantum_finite_model_diagnostic.py"
    "scripts/validate_multiscale_flagship_receipt.py"
    "DASHI.Environment.SurrogateCalibration"
    "DASHI.Environment.ValidationGovernance"
    "internal finite diagnostic and governance references only; no matched physical solver benchmark completed"

record BenchmarkBoundary : Set where
  constructor benchmark-boundary
  field
    protocolImplemented : Bool
    protocolImplementedIsTrue : protocolImplemented ≡ true
    finiteDiagnosticReproducible : Bool
    finiteDiagnosticReproducibleIsTrue : finiteDiagnosticReproducible ≡ true
    physicalMatchedQualitySuiteCompleted : Bool
    physicalMatchedQualitySuiteCompletedIsFalse :
      physicalMatchedQualitySuiteCompleted ≡ false
    runtimeAlonePromotesTheory : Bool
    runtimeAlonePromotesTheoryIsFalse : runtimeAlonePromotesTheory ≡ false
open BenchmarkBoundary public

canonicalBenchmarkBoundary : BenchmarkBoundary
canonicalBenchmarkBoundary =
  benchmark-boundary true refl true refl false refl false refl
