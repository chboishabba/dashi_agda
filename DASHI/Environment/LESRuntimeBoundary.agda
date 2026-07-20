module DASHI.Environment.LESRuntimeBoundary where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Environment.InversePlanning as Planning
import DASHI.Environment.ParetoPlanning as Pareto
import DASHI.Environment.QuantitiesConservation as Q
import DASHI.Environment.SpatialTransport as Spatial
import DASHI.Environment.SurrogateCalibration as Surrogate

------------------------------------------------------------------------
-- The formal repository owns contracts and promotion gates.  The LES runtime
-- owns raster/vector ingestion, numerical models, optimisation, and exports.

data RuntimeArtifactKind : Set where
  rasterLayer : RuntimeArtifactKind
  vectorLayer : RuntimeArtifactKind
  graphLayer : RuntimeArtifactKind
  timeSeries : RuntimeArtifactKind
  modelRunManifest : RuntimeArtifactKind
  surrogateArtifact : RuntimeArtifactKind
  optimisationPopulation : RuntimeArtifactKind
  reportArtifact : RuntimeArtifactKind

record RuntimeArtifact : Set where
  constructor mkRuntimeArtifact
  field
    artifactId : String
    kind : RuntimeArtifactKind
    uri : String
    contentHash : String
    crsOrCoordinateReference : String
    unitsManifest : List String
    producerVersion : String
    provenance : List String
open RuntimeArtifact public

record GISIngestionReceipt : Set where
  constructor mkGISIngestionReceipt
  field
    sourceFiles : List RuntimeArtifact
    scenarioCRS : String
    reprojectionRecorded : Bool
    geometryValidationRecorded : Bool
    nodataPolicyRecorded : Bool
    derivedLayers : List RuntimeArtifact
open GISIngestionReceipt public

record ModelAdapterReceipt : Set where
  constructor mkModelAdapterReceipt
  field
    adapterName : String
    authoritativeIdentity : Surrogate.ModelIdentity
    inputArtifacts : List RuntimeArtifact
    outputArtifacts : List RuntimeArtifact
    variableMapping : List String
    unitMapping : List String
    deterministicConfiguration : Bool
    runManifest : RuntimeArtifact
open ModelAdapterReceipt public

record PlanningRuntimeReceipt : Set where
  constructor mkPlanningRuntimeReceipt
  field
    gisIngestion : GISIngestionReceipt
    spatialNodes : List Spatial.SpatialNode
    modelAdapters : List ModelAdapterReceipt
    calibrationReceipts : List Surrogate.CalibrationReceipt
    conservation : Q.ConservationBundle
    candidatePlans : List Planning.Plan
    paretoResult : Pareto.FiniteParetoResult
    selectedFormalReceipt : Planning.PlanningReceipt
    outputArtifacts : List RuntimeArtifact
    auditManifest : RuntimeArtifact
open PlanningRuntimeReceipt public

record RuntimeBoundary : Set where
  constructor mkRuntimeBoundary
  field
    agdaOwnsContractsInvariantsAndPromotionGates : Bool
    lesOwnsNumericalExecutionAndGIS : Bool
    runtimeArtifactsRequireHashesAndProvenance : Bool
    runtimeCannotPromoteWithoutFormalReceipt : Bool
    formalReceiptDoesNotCertifyExternalDataByItself : Bool
    rendererIsDownstreamOfScientificState : Bool
open RuntimeBoundary public

canonicalRuntimeBoundary : RuntimeBoundary
canonicalRuntimeBoundary =
  mkRuntimeBoundary true true true true true true
