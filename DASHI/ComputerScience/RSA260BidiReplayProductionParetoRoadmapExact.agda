module DASHI.ComputerScience.RSA260BidiReplayProductionParetoRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiGF2FactorPacketFullPortfolioExact as Full
import DASHI.ComputerScience.RSA260BidiProductionGeneratorResidualAdapterExact as Production
import DASHI.ComputerScience.RSA260BidiProductionCompressedGeneratorResidualExact as Compressed

------------------------------------------------------------------------
-- RSA-260 REPLAY / PRODUCTION PARETO RECUT
--
-- The synthetic replay lane has crossed an important boundary:
--
--   * compact scalar/rank encodings were falsified for generator identity;
--   * coefficient-level residual replay was retained;
--   * the hybrid codec round-tripped discovery and independent synthetic sets;
--   * all 28 factor-mode layers / 224 factor rows are now compiled to concrete
--     formal basis/mask/expected-row terms at source level.
--
-- Therefore codec hardening is no longer the global critical path. Production
-- already has a raw coefficient-residual interface, and compression is explicitly
-- optional after same-object custody. The highest-alpha global target returns to
-- authentic A* / F.sols* acquisition while packed-byte welding and kernel
-- certification continue as orthogonal replay-hardening/certification lanes.
------------------------------------------------------------------------

fullPortfolioBoundary : Full.GF2FactorPacketFullPortfolioBoundary
fullPortfolioBoundary = Full.canonicalGF2FactorPacketFullPortfolioBoundary

productionBoundary : Production.ProductionGeneratorResidualBoundary
productionBoundary = Production.canonicalProductionGeneratorResidualBoundary

compressedBoundary : Compressed.ProductionCompressedGeneratorResidualBoundary
compressedBoundary = Compressed.canonicalProductionCompressedGeneratorResidualBoundary

data SyntheticReplayTarget : Set where
  weldPackedRuntimeBytesToFormalFactorConstructors : SyntheticReplayTarget
  provePackedEightBitRowRepresentationExact : SyntheticReplayTarget
  compileCertifiedFactorPacketsIntoHybridLayerCodec : SyntheticReplayTarget
  compareExactReplayCodecsOnSeparateCostAxesIfUseful : SyntheticReplayTarget
  obtainExactHeadKernelReceipt : SyntheticReplayTarget

firstSyntheticReplayTarget : SyntheticReplayTarget
firstSyntheticReplayTarget = weldPackedRuntimeBytesToFormalFactorConstructors

data ProductionTarget : Set where
  acquireSameObjectProjectedAStarBytes : ProductionTarget
  orAcquireSameObjectFSolsBytes : ProductionTarget
  authenticateArtifactSameObjectIdentity : ProductionTarget
  deriveOrDecodeGeneratorCoefficientResidual : ProductionTarget
  replayMksol : ProductionTarget
  recoverAndVerifyNonzeroKernelVector : ProductionTarget
  compileFactorCertificate : ProductionTarget

firstProductionTarget : ProductionTarget
firstProductionTarget = acquireSameObjectProjectedAStarBytes

data GlobalParetoTarget : Set where
  productionGeneratorArtifactAcquisition : GlobalParetoTarget
  syntheticReplayRepresentationHardening : GlobalParetoTarget
  certificationReceiptAcquisition : GlobalParetoTarget
  broaderFineIncidenceMatrixAcquisition : GlobalParetoTarget

firstGlobalParetoTarget : GlobalParetoTarget
firstGlobalParetoTarget = productionGeneratorArtifactAcquisition

record ReplayProductionParetoBoundary : Set where
  constructor replay-production-pareto-boundary
  field
    compactScalarRankReplayLanguageFalsified : Bool
    coefficientResidualRetainedForGeneratorSensitiveConsumers : Bool
    syntheticHybridCodecRuntimeRoundTripPaid : Bool
    fullTwentyEightFactorLayerSourcePortfolioCompiled : Bool
    fullTwoHundredTwentyFourFactorRowSourceEqualitiesWritten : Bool
    exactHeadAgdaKernelReceiptObserved : Bool
    packedRuntimeByteWeldPaid : Bool
    sameObjectAStarBytesPaid : Bool
    sameObjectFSolsBytesPaid : Bool
    unifiedProductionGeneratorResidualCustodyPaid : Bool
    rawAuthenticatedCoefficientRouteRequiresPackedCodec : Bool
    compressionRemainsOptionalAfterAuthenticCustody : Bool
    replayHardeningStillBlocksProductionAcquisition : Bool
    productionArtifactAcquisitionNowDominatesGlobalParetoFrontier : Bool
    broaderFineIncidenceMatrixAcquisitionStillOrthogonal : Bool
open ReplayProductionParetoBoundary public

canonicalReplayProductionParetoBoundary : ReplayProductionParetoBoundary
canonicalReplayProductionParetoBoundary =
  replay-production-pareto-boundary
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    true
    false
    true
    true

------------------------------------------------------------------------
-- Critical-path interpretation.
--
-- Synthetic replay language work has achieved its main design purpose: it
-- falsified lossy scalar summaries and retained a replayable coefficient-level
-- residual. Further codec work improves trust/storage/replay ergonomics but does
-- not need to complete before authentic generator bytes can enter the existing
-- raw coefficient interface.
------------------------------------------------------------------------

data ReplayHardeningMustFinishBeforeAStarAcquisition : Set where
data SourceCompletePortfolioMeansKernelCertified : Set where
data SyntheticReplayMeansProductionGeneratorCustody : Set where
data CompressionRequiredForFactorCertificate : Set where

replayHardeningDoesNotBlockAcquisition :
  ReplayHardeningMustFinishBeforeAStarAcquisition → ⊥
replayHardeningDoesNotBlockAcquisition ()

sourcePortfolioDoesNotCreateKernelCertification :
  SourceCompletePortfolioMeansKernelCertified → ⊥
sourcePortfolioDoesNotCreateKernelCertification ()

syntheticReplayDoesNotCreateProductionCustody :
  SyntheticReplayMeansProductionGeneratorCustody → ⊥
syntheticReplayDoesNotCreateProductionCustody ()

compressionDoesNotBecomeFactorCertificatePremise :
  CompressionRequiredForFactorCertificate → ⊥
compressionDoesNotBecomeFactorCertificatePremise ()
