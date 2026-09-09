module DASHI.Cognition.PNF.SensibLawOALCNativeShardResolutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawOALCLegislationParserInputContractExact as OALC

------------------------------------------------------------------------
-- OALC NATIVE SHARD RESOLUTION
--
-- Acquisition and source resolution remain native to SLR/Rust. Python is not
-- an OALC provider dependency: Python is retained only for the spaCy parser
-- stage after an exact retained source receipt exists.
--
-- Runtime target:
--
--   LegalFollow exact source demand
--      -> immutable OALC revision
--      -> discover Parquet shard set for that revision
--      -> native Rust projected scan for exact legislation row
--      -> retain exact text + digest + revision + resolution receipt
--      -> section slicing
--      -> spaCy (Python)
--      -> PNF (Rust)
--
-- Any shard-discovery/read/scan failure is a SOURCE_RESIDUAL and never source
-- absence, negative legal evidence, or semantic payment.
------------------------------------------------------------------------

data OALCNativeResolutionStage : Set where
  shardManifestDiscovery : OALCNativeResolutionStage
  shardProjectedScan : OALCNativeResolutionStage
  exactRowRetention : OALCNativeResolutionStage

data OALCNativeResolutionOutcome : Set where
  exactDocumentResolved : OALCNativeResolutionOutcome
  sourceResidual : OALCNativeResolutionOutcome
  completeScanNoExactRow : OALCNativeResolutionOutcome

record OALCParquetShardRef : Set where
  constructor oalc-parquet-shard-ref
  field
    datasetRevisionRef : String
    configRef : String
    splitRef : String
    shardRef : String
    shardSizeRef : String
    discoveryAuthority : String

open OALCParquetShardRef public

record OALCNativeShardDemand
    (demand : OALC.OALCLegislationSourceDemand) : Set where
  constructor oalc-native-shard-demand
  field
    immutableRevisionRef : String
    exactCitationRef : String
    exactSourceRef : String
    exactJurisdictionRef : String
    exactDocumentTypeRef : String
    projectedColumnsRef : String
    providerAuthority : String

open OALCNativeShardDemand public

record OALCNativeShardResolutionReceipt
    {dataset : OALC.OALCDatasetSelection}
    {demand : OALC.OALCLegislationSourceDemand}
    (document : OALC.OALCResolvedDocumentReceipt dataset demand) : Set where
  constructor oalc-native-shard-resolution-receipt
  field
    shardManifestRef : String
    scannedShardRefs : String
    exactRowIdentityRef : String
    nativeRuntimeRef : String
    resolutionPathRef : String
    acquisitionAuthority : String

open OALCNativeShardResolutionReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PythonDatasetsRequiredForAcquisition : Set where
data PythonAcquisitionCreatesSourceAuthority : Set where
data ShardReadFailureMeansSourceAbsent : Set where
data ShardManifestFailureMeansNegativeLegalEvidence : Set where
data PartialShardScanMayClaimCompleteAbsence : Set where
data NativeExactRowCreatesHistoricalEquivalence : Set where
data NativeExactRowCreatesAtomicGate : Set where

pythonDatasetsNotRequiredForAcquisition :
  PythonDatasetsRequiredForAcquisition → ⊥
pythonDatasetsNotRequiredForAcquisition ()

pythonAcquisitionDoesNotCreateAuthority :
  PythonAcquisitionCreatesSourceAuthority → ⊥
pythonAcquisitionDoesNotCreateAuthority ()

shardReadFailureDoesNotMeanSourceAbsent :
  ShardReadFailureMeansSourceAbsent → ⊥
shardReadFailureDoesNotMeanSourceAbsent ()

shardManifestFailureDoesNotCreateNegativeLegalEvidence :
  ShardManifestFailureMeansNegativeLegalEvidence → ⊥
shardManifestFailureDoesNotCreateNegativeLegalEvidence ()

partialShardScanCannotClaimCompleteAbsence :
  PartialShardScanMayClaimCompleteAbsence → ⊥
partialShardScanCannotClaimCompleteAbsence ()

nativeExactRowDoesNotCreateHistoricalEquivalence :
  NativeExactRowCreatesHistoricalEquivalence → ⊥
nativeExactRowDoesNotCreateHistoricalEquivalence ()

nativeExactRowDoesNotCreateAtomicGate :
  NativeExactRowCreatesAtomicGate → ⊥
nativeExactRowDoesNotCreateAtomicGate ()

record OALCNativeShardResolutionBoundary : Set where
  constructor oalc-native-shard-resolution-boundary
  field
    rustOwnsAcquisition : Bool
    pythonReservedForSpacy : Bool
    immutableRevisionRequired : Bool
    projectedExactRowScanRequired : Bool
    exactRowRetainedBeforeParser : Bool
    partialScanMayClaimAbsence : Bool
    providerFailureCreatesNegativeEvidence : Bool
    resolvedLatestKnownTextPaysHistoricalEquivalence : Bool
    resolutionCreatesAtomicGate : Bool

canonicalOALCNativeShardResolutionBoundary :
  OALCNativeShardResolutionBoundary
canonicalOALCNativeShardResolutionBoundary =
  oalc-native-shard-resolution-boundary
    true true true true true false false false false
