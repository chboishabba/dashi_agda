module DASHI.Reasoning.QuantumCryptoHistoryIndexedAlgorithmModelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.HistoryTimeIndexedAlgorithmModelExact as Model
import DASHI.Crypto.AlgorithmRelativeRecoveryCostExact as Cost
import DASHI.Crypto.ComputationalCandidateFibreExact as Fibre
import DASHI.Algebra.Quantum.GeneralShor as Shor

------------------------------------------------------------------------
-- QUANTUM / CRYPTO HISTORY-INDEXED ALGORITHM-MODEL SEAM
--
-- Candidate fibres, recovery architectures, Shor machines, probability models,
-- and physical implementations are different model coordinates.  Updating one
-- is a governed model revision, not a retrospective rewrite of earlier results.
------------------------------------------------------------------------

data ComputationModelKind : Set where
  candidateFibreVerifier
  classicalRecoveryArchitecture
  shorPeriodFindingMachine
  shorProbabilityModel
  physicalQuantumImplementation
  : ComputationModelKind

record QuantumCryptoModelVersion : Set where
  constructor quantumCryptoModelVersion
  field
    kind : ComputationModelKind
    versionTag : String
    implementationReference : String
    assumptionsReference : String

open QuantumCryptoModelVersion public

record CryptoRecoveryAssessment : Set₁ where
  constructor cryptoRecoveryAssessment
  field
    architecture : Cost.RecoveryArchitecture
    candidateFibreReference : String
    transcriptReference : String
    modelVersion : QuantumCryptoModelVersion
    assessmentReference : String

open CryptoRecoveryAssessment public

record ShorExecutionAssessment : Set₁ where
  constructor shorExecutionAssessment
  field
    problemReference : String
    machineReference : String
    sampleHistoryReference : String
    probabilityEvidenceReference : String
    physicalImplementationReference : String
    modelVersion : QuantumCryptoModelVersion
    assessmentReference : String

open ShorExecutionAssessment public

------------------------------------------------------------------------
-- Explicit cross-model comparison receipts.
------------------------------------------------------------------------

record RecoveryModelRevision : Set₁ where
  constructor recoveryModelRevision
  field
    before after : CryptoRecoveryAssessment
    externalRevisionAuthority : String
    sameEvidenceHistory : transcriptReference before ≡ transcriptReference after
    costModelComparisonReference : String
    revisionReference : String

open RecoveryModelRevision public

record ShorModelRevision : Set₁ where
  constructor shorModelRevision
  field
    before after : ShorExecutionAssessment
    externalRevisionAuthority : String
    sameSampleHistory : sampleHistoryReference before ≡ sampleHistoryReference after
    probabilityComparisonReference : String
    implementationComparisonReference : String
    revisionReference : String

open ShorModelRevision public

------------------------------------------------------------------------
-- Existing mathematical boundaries remain authoritative.
------------------------------------------------------------------------

candidateCountShrinkDoesNotByItselfGiveCostImprovement : Bool
candidateCountShrinkDoesNotByItselfGiveCostImprovement = false

injectivePublicMapDoesNotByItselfGiveEfficientInverse : Bool
injectivePublicMapDoesNotByItselfGiveEfficientInverse = false

successfulShorSampleDoesNotByItselfGiveProbabilityBound : Bool
successfulShorSampleDoesNotByItselfGiveProbabilityBound = false

------------------------------------------------------------------------
-- Hard boundary.
------------------------------------------------------------------------

record QuantumCryptoHistoryIndexedModelBoundary : Set where
  constructor quantumCryptoHistoryIndexedModelBoundary
  field
    changedAttackerModelRewritesOldTranscript : Bool
    changedAttackerModelRewritesOldTranscriptIsFalse :
      changedAttackerModelRewritesOldTranscript ≡ false
    changedRecoveryCostModelRewritesOldCandidateFibre : Bool
    changedRecoveryCostModelRewritesOldCandidateFibreIsFalse :
      changedRecoveryCostModelRewritesOldCandidateFibre ≡ false
    changedShorMachineRewritesOldExecutionSample : Bool
    changedShorMachineRewritesOldExecutionSampleIsFalse :
      changedShorMachineRewritesOldExecutionSample ≡ false
    changedProbabilityModelTurnsOldSuccessIntoProbabilityTheorem : Bool
    changedProbabilityModelTurnsOldSuccessIntoProbabilityTheoremIsFalse :
      changedProbabilityModelTurnsOldSuccessIntoProbabilityTheorem ≡ false
    physicalImplementationIdentityFollowsFromAbstractMachineIdentity : Bool
    physicalImplementationIdentityFollowsFromAbstractMachineIdentityIsFalse :
      physicalImplementationIdentityFollowsFromAbstractMachineIdentity ≡ false

canonicalQuantumCryptoHistoryIndexedModelBoundary :
  QuantumCryptoHistoryIndexedModelBoundary
canonicalQuantumCryptoHistoryIndexedModelBoundary =
  quantumCryptoHistoryIndexedModelBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
