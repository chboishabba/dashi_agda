module DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecCrossValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecExact as Codec

------------------------------------------------------------------------
-- HYBRID REPLAY CODEC ROBUSTNESS CROSS-VALIDATION
--
-- Reuse the earlier candidate-robustness portfolio shape:
--   * eight independent X/Y seed pairs under the identity preparation;
--   * four preparation adapters at the baseline projection pair.
--
-- For every recovered shared generator, run the exact hybrid coefficient codec
-- and check full coefficient-array reconstruction plus packed SHA equality.
------------------------------------------------------------------------

codecBoundary : Codec.CoefficientHybridReplayCodecBoundary
codecBoundary = Codec.canonicalCoefficientHybridReplayCodecBoundary

record HybridCodecCrossValidationRuntimeReceipt : Set where
  constructor hybrid-codec-cross-validation-runtime-receipt
  field
    runtimePath : String
    runtimeGitBlob : String
    runtimeSHA256 : String
    outputPath : String
    outputGitBlob : String
    outputSHA256 : String
    projectionSeedRuns : Nat
    preparationAdapterRuns : Nat
    totalRuns : Nat
    minimumBitsSaved : Nat
    maximumBitsSaved : Nat
    allRoundTripsExact : Bool
    allReconstructedSHAsMatch : Bool
    everyRunCompressedBelowRaw : Bool
    exactLocalRuntimeExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open HybridCodecCrossValidationRuntimeReceipt public

currentHybridCodecCrossValidationRuntimeReceipt :
  HybridCodecCrossValidationRuntimeReceipt
currentHybridCodecCrossValidationRuntimeReceipt =
  hybrid-codec-cross-validation-runtime-receipt
    "/mnt/data/rsa260_coefficient_hybrid_codec_crossvalidation.py"
    "f88cd04e176f86eaec7a41414d52dae46536a4ea"
    "3dfaab77083e1385488a56e0498c5db281fec67b6ca7ccfb8a1db5de328958a9"
    "/mnt/data/rsa260_coefficient_hybrid_codec_crossvalidation.json"
    "243f11f5645710359f1aeaeffa7197e0cd60a228"
    "71d6a48686fb8c927454755f9ea9799730c6fe51b8e85a982e91929c8c7f04e6"
    8
    4
    12
    56
    159
    true
    true
    true
    true
    false

record HybridCodecCrossValidationBoundary : Set where
  constructor hybrid-codec-cross-validation-boundary
  field
    discoveryPortfolioRoundTripInherited : Bool
    independentProjectionSeedFamilyChecked : Bool
    independentPreparationAdapterFamilyChecked : Bool
    allTwelveRoundTripsExact : Bool
    allTwelveDigestChecksPaid : Bool
    allTwelveCompressBelowRaw : Bool
    descriptionExecutionWitnessSeparationRetained : Bool
    crossValidationProvesGenericCodecTheorem : Bool
    crossValidationUsesProductionRSA260Generator : Bool
    crossValidationProvesGloballyOptimalCodec : Bool
open HybridCodecCrossValidationBoundary public

canonicalHybridCodecCrossValidationBoundary : HybridCodecCrossValidationBoundary
canonicalHybridCodecCrossValidationBoundary =
  hybrid-codec-cross-validation-boundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false

------------------------------------------------------------------------
-- Keep synthetic theorem work and production acquisition explicitly parallel.
------------------------------------------------------------------------

data HybridCodecCrossValidationResidual : Set where
  proveGenericGF2RowBasisCodecRoundTrip : HybridCodecCrossValidationResidual
  compareAlternativeExactCodecsOnThreeCostAxes : HybridCodecCrossValidationResidual
  deriveAdmissibleCodecSearchHeuristicIfAvailable : HybridCodecCrossValidationResidual
  compileCodecIntoProductionGeneratorResidualInterface : HybridCodecCrossValidationResidual

firstHybridCodecCrossValidationResidual : HybridCodecCrossValidationResidual
firstHybridCodecCrossValidationResidual = proveGenericGF2RowBasisCodecRoundTrip

data HybridCodecProductionResidual : Set where
  acquireSameObjectProjectedAStarBytes : HybridCodecProductionResidual
  orAcquireSameObjectFSolsBytes : HybridCodecProductionResidual
  authenticateGeneratorResidualCustody : HybridCodecProductionResidual
  replayMksolFromAuthenticatedGeneratorResidual : HybridCodecProductionResidual
  recoverAndVerifyNonzeroKernelVector : HybridCodecProductionResidual
  compileFactorCertificate : HybridCodecProductionResidual

firstHybridCodecProductionResidual : HybridCodecProductionResidual
firstHybridCodecProductionResidual = acquireSameObjectProjectedAStarBytes

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data TwelveSyntheticPassesMeanGenericProof : Set where
data CodecCrossValidationMeansProductionCustody : Set where
data CompressionSavingsMeanGlobalOptimality : Set where

syntheticPassesDoNotCreateGenericProof : TwelveSyntheticPassesMeanGenericProof → ⊥
syntheticPassesDoNotCreateGenericProof ()

codecCrossValidationDoesNotCreateProductionCustody :
  CodecCrossValidationMeansProductionCustody → ⊥
codecCrossValidationDoesNotCreateProductionCustody ()

compressionSavingsDoNotCreateGlobalOptimality :
  CompressionSavingsMeanGlobalOptimality → ⊥
compressionSavingsDoNotCreateGlobalOptimality ()
