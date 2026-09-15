module DASHI.ComputerScience.RSA260BidiProductionCompressedGeneratorResidualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiProductionGeneratorResidualAdapterExact as Production
import DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecExact as Codec
import DASHI.ComputerScience.RSA260BidiGF2RowCodecMatrixLiftExact as Lift

------------------------------------------------------------------------
-- OPTIONAL COMPRESSED REPRESENTATION FOR PRODUCTION GENERATOR RESIDUALS
--
-- Production acquisition semantics do not change: authentic A* or F.sols*
-- must first pay the existing same-object generator-coefficient custody.
-- Compression is an optional storage/replay representation layered AFTER that
-- payment.  It is admissible only with an exact decode/round-trip receipt.
--
-- This prevents the synthetic codec from becoming a new production premise or
-- from manufacturing coefficient custody that has not been acquired.
------------------------------------------------------------------------

productionBoundary : Production.ProductionGeneratorResidualBoundary
productionBoundary = Production.canonicalProductionGeneratorResidualBoundary

codecBoundary : Codec.CoefficientHybridReplayCodecBoundary
codecBoundary = Codec.canonicalCoefficientHybridReplayCodecBoundary

matrixLiftBoundary : Lift.GF2RowCodecMatrixLiftBoundary
matrixLiftBoundary = Lift.canonicalGF2RowCodecMatrixLiftBoundary

record ExactGeneratorCodecReceipt : Set where
  constructor exact-generator-codec-receipt
  field
    codecReference : String
    encoderExecutedOnSameObjectCoefficients : Bool
    decoderExecutedOnEncodedPayload : Bool
    decodedCoefficientBytesEqualSource : Bool
    sourceAndDecodedGeneratorDigestEqual : Bool

    encoderPaid : encoderExecutedOnSameObjectCoefficients ≡ true
    decoderPaid : decoderExecutedOnEncodedPayload ≡ true
    byteEqualityPaid : decodedCoefficientBytesEqualSource ≡ true
    digestEqualityPaid : sourceAndDecodedGeneratorDigestEqual ≡ true
open ExactGeneratorCodecReceipt public

record CompressedGeneratorResidualCustody
    (source : Production.GeneratorCoefficientResidualCustody) : Set where
  constructor compressed-generator-residual-custody
  field
    exactCodec : ExactGeneratorCodecReceipt
    compressedPayloadAvailable : Bool
    originalCoefficientCustodyRetained : Bool

    compressedPayloadPaid : compressedPayloadAvailable ≡ true
    originalCustodyRetainedPaid : originalCoefficientCustodyRetained ≡ true
open CompressedGeneratorResidualCustody public

record CompressedResidualConsumerAdmission
    {source : Production.GeneratorCoefficientResidualCustody}
    (compressed : CompressedGeneratorResidualCustody source) : Set where
  constructor compressed-residual-consumer-admission
  field
    decodeToCoefficientResidualAdmitted : Bool
    generatorIdentityConsumerAdmittedAfterDecode : Bool
    mksolReplayMayConsumeDecodedCoefficients : Bool

    decodePaid : decodeToCoefficientResidualAdmitted ≡ true
    generatorConsumerPaid : generatorIdentityConsumerAdmittedAfterDecode ≡ true
    mksolInputPaid : mksolReplayMayConsumeDecodedCoefficients ≡ true
open CompressedResidualConsumerAdmission public

exactCompressedCustodyPaysDecodedConsumers :
  {source : Production.GeneratorCoefficientResidualCustody} →
  (compressed : CompressedGeneratorResidualCustody source) →
  CompressedResidualConsumerAdmission compressed
exactCompressedCustodyPaysDecodedConsumers compressed =
  compressed-residual-consumer-admission
    true true true
    refl refl refl

------------------------------------------------------------------------
-- Current production state remains unpaid.  The synthetic codec receipt does
-- not instantiate ExactGeneratorCodecReceipt for RSA-260 production bytes.
------------------------------------------------------------------------

record CurrentCompressedProductionState : Set where
  constructor current-compressed-production-state
  field
    authenticGeneratorResidualCustodyPaid : Bool
    exactProductionCodecRoundTripPaid : Bool
    compressedProductionPayloadPaid : Bool
    productionMksolReplayPaid : Bool
open CurrentCompressedProductionState public

currentCompressedProductionState : CurrentCompressedProductionState
currentCompressedProductionState =
  current-compressed-production-state false false false false

record ProductionCompressedGeneratorResidualBoundary : Set where
  constructor production-compressed-generator-residual-boundary
  field
    productionGeneratorResidualInterfaceInherited : Bool
    syntheticHybridCodecAvailable : Bool
    genericEightRowCodecLiftAvailable : Bool
    compressionIsOptionalAfterAuthenticCustody : Bool
    exactRoundTripRequiredForProductionCompressedUse : Bool
    compressedPayloadCanBeDecodedBeforeGeneratorConsumers : Bool
    compressionChangesSameObjectAcquisitionRequirement : Bool
    syntheticCodecCreatesProductionCodecReceipt : Bool
    compressedRepresentationEliminatesNeedForCoefficientSemantics : Bool
    currentProductionCompressedResidualPaid : Bool
open ProductionCompressedGeneratorResidualBoundary public

canonicalProductionCompressedGeneratorResidualBoundary :
  ProductionCompressedGeneratorResidualBoundary
canonicalProductionCompressedGeneratorResidualBoundary =
  production-compressed-generator-residual-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- Parallel live queues remain explicit.
------------------------------------------------------------------------

data ProductionCompressedGeneratorResidualResidual : Set where
  proveGF2BasisCoordinateRowCodecExact : ProductionCompressedGeneratorResidualResidual
  provePackedGeneratorCodecBitLevelRoundTrip : ProductionCompressedGeneratorResidualResidual
  acquireSameObjectProjectedAStarBytes : ProductionCompressedGeneratorResidualResidual
  orAcquireSameObjectFSolsBytes : ProductionCompressedGeneratorResidualResidual
  authenticateGeneratorResidualCustody : ProductionCompressedGeneratorResidualResidual
  executeCodecOnAuthenticatedGeneratorIfUseful : ProductionCompressedGeneratorResidualResidual
  replayMksolFromDecodedGeneratorResidual : ProductionCompressedGeneratorResidualResidual
  recoverAndVerifyNonzeroKernelVector : ProductionCompressedGeneratorResidualResidual
  compileFactorCertificate : ProductionCompressedGeneratorResidualResidual

firstProductionCompressedGeneratorResidualResidual :
  ProductionCompressedGeneratorResidualResidual
firstProductionCompressedGeneratorResidualResidual =
  proveGF2BasisCoordinateRowCodecExact

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data CompressionMeansAcquisition : Set where
data SyntheticRoundTripMeansProductionRoundTrip : Set where
data CompressedPayloadMeansCoefficientSemantics : Set where
data CodecSavingsMeansFactorCertificate : Set where

compressionDoesNotCreateAcquisition : CompressionMeansAcquisition → ⊥
compressionDoesNotCreateAcquisition ()

syntheticRoundTripDoesNotCreateProductionRoundTrip :
  SyntheticRoundTripMeansProductionRoundTrip → ⊥
syntheticRoundTripDoesNotCreateProductionRoundTrip ()

compressedPayloadDoesNotCreateCoefficientSemantics :
  CompressedPayloadMeansCoefficientSemantics → ⊥
compressedPayloadDoesNotCreateCoefficientSemantics ()

codecSavingsDoesNotCreateFactorCertificate : CodecSavingsMeansFactorCertificate → ⊥
codecSavingsDoesNotCreateFactorCertificate ()
