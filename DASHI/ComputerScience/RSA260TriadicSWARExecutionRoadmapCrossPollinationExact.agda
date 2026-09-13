module DASHI.ComputerScience.RSA260TriadicSWARExecutionRoadmapCrossPollinationExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260SnowballPrimaryAttributionExact as RSA
import DASHI.ComputerScience.RSA260GNFSStageRunReceiptExact as Stage
import DASHI.ComputerScience.RSA260GNFSRunParameterArtifactSnowballExact as Params
import DASHI.ComputerScience.TriadicCompiledScalarU8RuntimeExact as Scalar
import DASHI.ComputerScience.TriadicSupportMaskSWARExecutionExact as SupportSWAR
import DASHI.ComputerScience.TriadicPrefixSWARExecutionExact as PrefixSWAR
import DASHI.ComputerScience.TriadicSignCompactionSWARExecutionExact as EncodeSWAR

------------------------------------------------------------------------
-- RSA-260 / TRIADIC SWAR ROADMAP CROSS-POLLINATION
--
-- The triadic codec work has now paid a reusable execution-validation pattern:
-- bounded ABI -> compiled scalar oracle -> exact source/blob receipt ->
-- packed-lane SWAR operation -> exhaustive/domain-bounded execution receipt.
--
-- This is directly useful as a METHOD for validating RSA-260 stage kernels,
-- especially the reported Block Wiedemann SIMD/CUDA lane.  It does not turn
-- the triadic codec into a GNFS kernel, does not reproduce RSA-260, and does
-- not identify Lu/Devin's executed source revision or executable.
------------------------------------------------------------------------

record ExecutionValidationPattern : Set where
  constructor execution-validation-pattern
  field
    boundedCarrier : Bool
    compiledScalarOracle : Bool
    exactSourceBlobBound : Bool
    packedLaneExecution : Bool
    domainCheckedAgainstOracle : Bool
    backendIdentitySeparatedFromSemantics : Bool
open ExecutionValidationPattern public

triadicExecutionValidationPattern : ExecutionValidationPattern
triadicExecutionValidationPattern = execution-validation-pattern
  true true true true true true

record RSAReuseBoundary : Set where
  constructor rsa-reuse-boundary
  field
    reusableValidationPattern : Bool
    reportedBlockWiedemannSIMDParameterRetained : Bool
    reportedCUDAImplementationRetained : Bool
    reportedNCCLCommunicationRetained : Bool
    triadicSWARIsBlockWiedemannKernel : Bool
    triadicCodecPaysGNFSReproduction : Bool
    triadicCodecPaysFactorArithmeticKernelCertificate : Bool
    triadicCodecPaysExactExecutedRevision : Bool
    triadicCodecPaysIndependentRunReproduction : Bool
open RSAReuseBoundary public

canonicalRSAReuseBoundary : RSAReuseBoundary
canonicalRSAReuseBoundary = rsa-reuse-boundary
  true
  true true true
  false false false false false

------------------------------------------------------------------------
-- Existing RSA carriers remain authoritative for the RSA lane.
------------------------------------------------------------------------

rsaPrimaryBoundary : RSA.RSA260SnowballBoundary
rsaPrimaryBoundary = RSA.canonicalRSA260SnowballBoundary

rsaLinearAlgebraRun : Stage.StageRunReceipt
rsaLinearAlgebraRun = Stage.rsa260LinearAlgebraRun

rsaLinearAlgebraParameters : Params.RunParameterReceipt
rsaLinearAlgebraParameters = Params.rsa260LinearAlgebraParameters

compiledScalarCodecReceipt : Scalar.CompiledScalarRuntimeReceipt
compiledScalarCodecReceipt = Scalar.triadicCompiledScalarU8Runtime

supportSWARReceipt : SupportSWAR.SWARExecutionReceipt
supportSWARReceipt = SupportSWAR.triadicSupportMaskSWARExecution

prefixSWARReceipt : PrefixSWAR.PrefixSWARExecutionReceipt
prefixSWARReceipt = PrefixSWAR.triadicPrefixSWARExecution

factorizedEncodeSWARReceipt : EncodeSWAR.SignCompactionSWARExecutionReceipt
factorizedEncodeSWARReceipt = EncodeSWAR.triadicSignCompactionSWARExecution

------------------------------------------------------------------------
-- Roadmap: what the triadic tranche changes for RSA-260.
------------------------------------------------------------------------

record RSA260ExecutionRoadmapBoundary : Set where
  constructor rsa260-execution-roadmap-boundary
  field
    sourceAttributionAndStageRunSeparation : Bool
    exactPublishedRunParametersRetained : Bool
    reusableBoundedABIValidationMethodAvailable : Bool
    reusableScalarOracleMethodAvailable : Bool
    reusablePackedLaneExecutionReceiptMethodAvailable : Bool
    exactLuDevinSourceRevisionBound : Bool
    exactRSA260ExecutableBound : Bool
    blockWiedemannKernelIndependentlyReproduced : Bool
    latticeSieveKernelIndependentlyReproduced : Bool
    squareRootKernelIndependentlyReproduced : Bool
    fullGNFSRunIndependentlyReproduced : Bool
    factorIdentityKernelCertifiedInDASHI : Bool
open RSA260ExecutionRoadmapBoundary public

currentRSA260ExecutionRoadmapBoundary : RSA260ExecutionRoadmapBoundary
currentRSA260ExecutionRoadmapBoundary = rsa260-execution-roadmap-boundary
  true true
  true true true
  false false false false false false false

------------------------------------------------------------------------
-- The next RSA implementation target is therefore NOT another provenance
-- owner.  It is a stage-local executable oracle/receipt, preferably for the
-- published Block Wiedemann lane because that stage already exposes width,
-- SIMD, CUDA and NCCL coordinates in the primary run parameters.
------------------------------------------------------------------------

record NextRSAStageTarget : Set where
  constructor next-rsa-stage-target
  field
    stage : String
    publishedParameterCarrierAvailable : Bool
    exactAlgorithmLineageAvailable : Bool
    exactExecutedSourceAvailable : Bool
    independentExecutableOracleAvailable : Bool
    packedOrSIMDValidationPatternReusable : Bool
open NextRSAStageTarget public

blockWiedemannNextTarget : NextRSAStageTarget
blockWiedemannNextTarget = next-rsa-stage-target
  "RSA-260 Block Wiedemann linear algebra: m=n=512, two width-256 sequences, simd=256, mm_impl=cuda, comm_impl=nccl"
  true true false false true

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data TriadicSWARImpliesRSAReproduction : Set where
data SamePackedExecutionPatternImpliesSameAlgorithm : Set where
data SIMDParameterImpliesExactSIMDImplementation : Set where
data CUDAParameterImpliesExecutableBound : Set where
data PublishedRunParametersImpliesIndependentReproduction : Set where
data ReusableValidationPatternImpliesFactorKernelCertificate : Set where

triadicSWARDoesNotReproduceRSA : TriadicSWARImpliesRSAReproduction → ⊥
triadicSWARDoesNotReproduceRSA ()

packedPatternDoesNotIdentifyAlgorithm : SamePackedExecutionPatternImpliesSameAlgorithm → ⊥
packedPatternDoesNotIdentifyAlgorithm ()

simdParameterDoesNotBindImplementation : SIMDParameterImpliesExactSIMDImplementation → ⊥
simdParameterDoesNotBindImplementation ()

cudaParameterDoesNotBindExecutable : CUDAParameterImpliesExecutableBound → ⊥
cudaParameterDoesNotBindExecutable ()

parametersDoNotCreateIndependentRun : PublishedRunParametersImpliesIndependentReproduction → ⊥
parametersDoNotCreateIndependentRun ()

validationMethodDoesNotCreateFactorCertificate :
  ReusableValidationPatternImpliesFactorKernelCertificate → ⊥
validationMethodDoesNotCreateFactorCertificate ()
