module DASHI.ComputerScience.RSA260BidiKrylovReachableRankExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiFineIncidenceDefectCoverageExact as Coverage
import DASHI.ComputerScience.RSA260CADOBlockWiedemannArtifactSchemaSnowballExact as CADO
import DASHI.ComputerScience.RSA260BlockWiedemannProductionScaleReconstructionExact as Scale

------------------------------------------------------------------------
-- BIDI DYNAMIC FIBRE: REACHABLE BLOCK-KRYLOV RANK
--
-- The static fine-incidence experiments show that the same shape, exact row
-- degree profile, rank, and left-nullity can have very different generator
-- complexity.  This owner inserts the missing dynamic coordinate:
--
--   fine incidence
--        -> reachable block-Krylov span r_k
--        -> shared-generator degree d.
--
-- Synthetic executable observation at k=80, block width 8:
--
--   d - ceil(r_80 / 8) in {0,1,2}
--
-- on the tested defect-coverage / preparation portfolio.
--
-- This is an experimental envelope, not a theorem saying
-- d = ceil(r_k / blockWidth) + c, and not a production RSA-260 measurement.
-- Its production consequence is acquisition-oriented: an authentic CADO A*
-- Krylov-sequence artifact can constrain dynamic reachable-span geometry even
-- when the original sparse matrix bytes have not yet been acquired.
------------------------------------------------------------------------

coverageBoundary : Coverage.DefectCoverageInterpretationBoundary
coverageBoundary = Coverage.canonicalDefectCoverageInterpretationBoundary

cadoArtifactSchema : CADO.CADOBlockWiedemannArtifactSchema
cadoArtifactSchema = CADO.currentCADOBlockWiedemannArtifactSchema

productionScaleBoundary : Scale.ProductionScaleReconstructionBoundary
productionScaleBoundary = Scale.canonicalProductionScaleReconstructionBoundary

------------------------------------------------------------------------
-- Exact runtime provenance.
------------------------------------------------------------------------

record KrylovReachableRankRuntimeSource : Set where
  constructor krylov-reachable-rank-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    exactCommittedBlobExecuted : Bool
open KrylovReachableRankRuntimeSource public

currentKrylovReachableRankRuntimeSource : KrylovReachableRankRuntimeSource
currentKrylovReachableRankRuntimeSource = krylov-reachable-rank-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_krylov_reachable_rank.py"
  "3041fe338836b93c6e2e38e1b15de63f73215825"
  "b4fd8b1fef6f31a28b227b42cde1bd47ac74fb5f"
  true

------------------------------------------------------------------------
-- Synthetic dynamic-rank receipt.
------------------------------------------------------------------------

record KrylovReachableRankReceipt : Set where
  constructor krylov-reachable-rank-receipt
  field
    carrierRows : Nat
    carrierColumns : Nat
    blockWidth : Nat
    horizon : Nat
    defectCoverageLevels : Nat
    preparationFamilies : Nat
    totalRuns : Nat
    minimumObservedReachableRank : Nat
    maximumObservedReachableRank : Nat
    minimumObservedGeneratorDegree : Nat
    maximumObservedGeneratorDegree : Nat
    minimumDegreeMinusCeiling : Nat
    maximumDegreeMinusCeiling : Nat
    allObservedOffsetsWithinZeroToTwo : Bool
open KrylovReachableRankReceipt public

currentKrylovReachableRankReceipt : KrylovReachableRankReceipt
currentKrylovReachableRankReceipt = krylov-reachable-rank-receipt
  924 512
  8 80
  4 2 8
  119 512
  16 66
  0 2
  true

------------------------------------------------------------------------
-- Production diagnostic consequence.
------------------------------------------------------------------------

data FineIncidenceBearingArtifact : Set where
  sparseMatrixArtifact : FineIncidenceBearingArtifact
  balancingPermutationArtifact : FineIncidenceBearingArtifact
  krylovSequenceArtifact : FineIncidenceBearingArtifact
  generatorArtifact : FineIncidenceBearingArtifact

record ArtifactDiagnosticPower : Set where
  constructor artifact-diagnostic-power
  field
    artifact : FineIncidenceBearingArtifact
    paysDirectIncidenceGeometry : Bool
    paysPreparationGeometry : Bool
    paysDynamicReachableSpan : Bool
    paysRealizedRecurrenceGeometry : Bool
    paysMatrixCustody : Bool
open ArtifactDiagnosticPower public

matrixDiagnosticPower : ArtifactDiagnosticPower
matrixDiagnosticPower = artifact-diagnostic-power
  sparseMatrixArtifact true false false false true

balancingDiagnosticPower : ArtifactDiagnosticPower
balancingDiagnosticPower = artifact-diagnostic-power
  balancingPermutationArtifact false true false false false

krylovSequenceDiagnosticPower : ArtifactDiagnosticPower
krylovSequenceDiagnosticPower = artifact-diagnostic-power
  krylovSequenceArtifact false false true false false

generatorDiagnosticPower : ArtifactDiagnosticPower
generatorDiagnosticPower = artifact-diagnostic-power
  generatorArtifact false false false true false

record DynamicRankInterpretationBoundary : Set where
  constructor dynamic-rank-interpretation-boundary
  field
    fineIncidenceCanChangeReachableKrylovRank : Bool
    reachableRankTracksTestedGeneratorScaleClosely : Bool
    observedZeroToTwoSlackIsUniversalTheorem : Bool
    authenticKrylovSequenceCanPayDynamicSpanDiagnostic : Bool
    authenticKrylovSequencePaysSparseMatrixBytes : Bool
    authenticKrylovSequencePaysBalancingIdentity : Bool
    authenticKrylovSequencePaysHistoricalMatrixIdentity : Bool
    productionGeneratorLengthSuggestsGenericScale : Bool
    productionReachableRankMeasuredByThisOwner : Bool
open DynamicRankInterpretationBoundary public

canonicalDynamicRankInterpretationBoundary : DynamicRankInterpretationBoundary
canonicalDynamicRankInterpretationBoundary = dynamic-rank-interpretation-boundary
  true
  true
  false
  true
  false
  false
  false
  true
  false

------------------------------------------------------------------------
-- Highest-alpha residual.
------------------------------------------------------------------------

data DynamicRankResidual : Set where
  acquireSameObjectKrylovSequenceArtifact : DynamicRankResidual
  estimateProductionReachableRankFromSameObjectSequence : DynamicRankResidual
  compareProductionReachableRankToGeneratorScale : DynamicRankResidual
  recoverProductionMatrixAfterDynamicDiagnostic : DynamicRankResidual

firstDynamicRankResidual : DynamicRankResidual
firstDynamicRankResidual = acquireSameObjectKrylovSequenceArtifact

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SyntheticSlackImpliesProductionFormula : Set where
data KrylovSequenceImpliesMatrixCustody : Set where
data DynamicSpanImpliesHistoricalIdentity : Set where
data ProductionGeneratorLengthImpliesMeasuredReachableRank : Set where

syntheticSlackDoesNotCreateProductionFormula : SyntheticSlackImpliesProductionFormula → ⊥
syntheticSlackDoesNotCreateProductionFormula ()

krylovSequenceDoesNotCreateMatrixCustody : KrylovSequenceImpliesMatrixCustody → ⊥
krylovSequenceDoesNotCreateMatrixCustody ()

dynamicSpanDoesNotCreateHistoricalIdentity : DynamicSpanImpliesHistoricalIdentity → ⊥
dynamicSpanDoesNotCreateHistoricalIdentity ()

productionGeneratorLengthDoesNotMeasureReachableRank : ProductionGeneratorLengthImpliesMeasuredReachableRank → ⊥
productionGeneratorLengthDoesNotMeasureReachableRank ()
