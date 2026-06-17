module DASHI.Interop.PNFSpectralNumericABICore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Core.FormalStructureLawCore as Structure
import DASHI.Interop.PNFSpectralCoordinateRebuildability as Rebuild
import DASHI.Interop.PNFSpectralFieldCore as Core
import DASHI.Interop.PNFSpectralFieldGraph as Graph
import DASHI.Interop.PNFSpectralRegistryAnchoring as Registry
import DASHI.Interop.PNFSpectralVectorIndex as Vector
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- PNF spectral numeric ABI boundary.
--
-- This module is the typed socket between the symbolic-relational PNF graph
-- and runtime numeric payloads.  It records only receipt-bound materialization:
-- row maps, residual edge tables, adjacency/Laplacian payloads, coordinate
-- tables, GEMV payloads, rebuildability, and admission gates.  Numeric arrays
-- remain candidate runtime artifacts; they do not promote semantic, evidence,
-- trading, security, legal, clinical, or deployment authority.

data PNFSpectralNumericABIStatus : Set where
  checkedNumericMaterializationCandidateOnly :
    PNFSpectralNumericABIStatus

data NumericABIComponent : Set where
  objectRegistryRowsComponent :
    NumericABIComponent

  rowMapBindingComponent :
    NumericABIComponent

  residualEdgeTableComponent :
    NumericABIComponent

  signedAdjacencyABIComponent :
    NumericABIComponent

  degreeRowABIComponent :
    NumericABIComponent

  laplacianABIComponent :
    NumericABIComponent

  eigenCoordinateABIComponent :
    NumericABIComponent

  gemvPayloadComponent :
    NumericABIComponent

  parityHashComponent :
    NumericABIComponent

  rebuildWitnessComponent :
    NumericABIComponent

  admissionGateComponent :
    NumericABIComponent

  numericNonAuthorityComponent :
    NumericABIComponent

canonicalNumericABIComponents : List NumericABIComponent
canonicalNumericABIComponents =
  objectRegistryRowsComponent
  ∷ rowMapBindingComponent
  ∷ residualEdgeTableComponent
  ∷ signedAdjacencyABIComponent
  ∷ degreeRowABIComponent
  ∷ laplacianABIComponent
  ∷ eigenCoordinateABIComponent
  ∷ gemvPayloadComponent
  ∷ parityHashComponent
  ∷ rebuildWitnessComponent
  ∷ admissionGateComponent
  ∷ numericNonAuthorityComponent
  ∷ []

------------------------------------------------------------------------
-- Runtime ABI vocabulary.

data NumericDType : Set where
  float32DType :
    NumericDType

  float64DType :
    NumericDType

  integerFixtureDType :
    NumericDType

data NumericArrayKind : Set where
  gemvMatrixA :
    NumericArrayKind

  gemvInputVectorZ :
    NumericArrayKind

  gemvOutputVectorB :
    NumericArrayKind

  signedAdjacencyMatrixW :
    NumericArrayKind

  diagonalDegreeMatrixD :
    NumericArrayKind

  laplacianMatrixL :
    NumericArrayKind

  eigenvalueVectorLambda :
    NumericArrayKind

  eigenvectorMatrixU :
    NumericArrayKind

  spectralCoordinateMatrixPhi :
    NumericArrayKind

data NumericMaterializationKind : Set where
  gemvMaterialization :
    NumericMaterializationKind

  signedAdjacencyMaterialization :
    NumericMaterializationKind

  laplacianMaterialization :
    NumericMaterializationKind

  eigenCoordinateMaterialization :
    NumericMaterializationKind

  fullSpectralPayloadMaterialization :
    NumericMaterializationKind

record NumericArrayDescriptor : Set where
  constructor numericArrayDescriptor
  field
    arrayKind :
      NumericArrayKind

    dtype :
      NumericDType

    rowCount :
      Nat

    columnCount :
      Nat

    arrayProfile :
      String

    dtypeBoundByReceipt :
      Bool

    shapeBoundByReceipt :
      Bool

open NumericArrayDescriptor public

record GraphVersionBinding : Set where
  constructor graphVersionBinding
  field
    graphVersion :
      String

    registryHash :
      Registry.VersionHash

    graphVersionBindsRegistry :
      Bool

    graphVersionBindsEdges :
      Bool

    graphVersionBindsCoordinates :
      Bool

open GraphVersionBinding public

record ParityHashBinding : Set where
  constructor parityHashBinding
  field
    parityHash :
      String

    hashAlgorithm :
      Registry.HashAlgorithm

    hashBindsSchema :
      Bool

    hashBindsDType :
      Bool

    hashBindsArrays :
      Bool

    hashBindsRowMap :
      Bool

    hashBindsReceipts :
      Bool

    hashBindsGraphVersion :
      Bool

    hashCarriesTruthAuthority :
      Bool

open ParityHashBinding public

------------------------------------------------------------------------
-- Row-map and object-registry binding.

record ReceiptIdBinding : Set where
  constructor receiptIdBinding
  field
    receiptId :
      String

    receiptObject :
      Vector.ObjectRef

    receiptRegistryRow :
      Registry.ObjectRegistryRow

    receiptBindsObject :
      Bool

    receiptBindsCurrentVersion :
      Bool

open ReceiptIdBinding public

record RowMapBinding : Set where
  constructor rowMapBinding
  field
    rowIndex :
      Nat

    rowObject :
      Vector.ObjectRef

    rowRegistry :
      Registry.ObjectRegistryRow

    rowObjectHash :
      Registry.VersionHash

    rowReceipt :
      ReceiptIdBinding

    rowGraphVersion :
      GraphVersionBinding

    rowMapSound :
      Bool

    rowRegistryAdmissible :
      Bool

    rowCandidateMaterialization :
      Bool

    rowObjectTruthAuthority :
      Bool

open RowMapBinding public

rowMapSoundCandidateOnly :
  ∀ row →
  rowMapSound row ≡ true →
  rowCandidateMaterialization row ≡ true →
  rowObjectTruthAuthority row ≡ false →
  Set
rowMapSoundCandidateOnly _ _ _ _ =
  Structure.FormalStructureAuthorityBoundary

------------------------------------------------------------------------
-- Residual edge table and signed adjacency ABI.

record ResidualEdgeTableRow : Set where
  constructor residualEdgeTableRow
  field
    edgeRowIndex :
      Nat

    edgeSourceRow :
      RowMapBinding

    edgeTargetRow :
      RowMapBinding

    edgeKind :
      Graph.PNFGraphEdgeKind

    edgeResidualLevel :
      Residual.ResidualLevel

    edgeWeight :
      Graph.SignedResidualWeight

    edgeWeightMatchesResidual :
      edgeWeight ≡ Graph.residualSignedWeight edgeResidualLevel

    edgeReceipt :
      ReceiptIdBinding

    edgeRowSound :
      Bool

    edgeCandidateMaterialization :
      Bool

    edgeTruthAuthority :
      Bool

open ResidualEdgeTableRow public

mkResidualEdgeTableRow :
  Nat →
  RowMapBinding →
  RowMapBinding →
  Graph.PNFGraphEdgeKind →
  Residual.ResidualLevel →
  ReceiptIdBinding →
  ResidualEdgeTableRow
mkResidualEdgeTableRow ix source target kind residual receipt =
  residualEdgeTableRow
    ix
    source
    target
    kind
    residual
    (Graph.residualSignedWeight residual)
    refl
    receipt
    true
    true
    false

record SignedAdjacencyABI : Set where
  constructor signedAdjacencyABI
  field
    adjacencyDescriptor :
      NumericArrayDescriptor

    adjacencyRows :
      List Rebuild.SignedAdjacencyRow

    adjacencyEdgeRows :
      List ResidualEdgeTableRow

    adjacencyRowMap :
      List RowMapBinding

    adjacencyColumnMap :
      List RowMapBinding

    adjacencyReceipt :
      ReceiptIdBinding

    adjacencyGraphVersion :
      GraphVersionBinding

    adjacencyParityHash :
      ParityHashBinding

    adjacencyABISound :
      Bool

    candidateSignedGraphMaterialization :
      Bool

    semanticGraphAuthority :
      Bool

open SignedAdjacencyABI public

adjacencyABICandidateOnly :
  ∀ abi →
  adjacencyABISound abi ≡ true →
  candidateSignedGraphMaterialization abi ≡ true →
  semanticGraphAuthority abi ≡ false →
  Set
adjacencyABICandidateOnly _ _ _ _ =
  Structure.FormalStructureAuthorityBoundary

------------------------------------------------------------------------
-- Degree rows and Laplacian ABI.

record DegreeRowABI : Set where
  constructor degreeRowABI
  field
    degreeRowIndex :
      Nat

    degreeRowMap :
      RowMapBinding

    degreeRow :
      Rebuild.AbsoluteDegreeOperatorRow

    signedAdjacencySource :
      SignedAdjacencyABI

    degreeReceipt :
      ReceiptIdBinding

    degreeBound :
      Bool

    degreeCandidateMaterialization :
      Bool

    importanceAuthority :
      Bool

open DegreeRowABI public

record LaplacianABI : Set where
  constructor laplacianABI
  field
    adjacency :
      SignedAdjacencyABI

    degreeDescriptor :
      NumericArrayDescriptor

    laplacianDescriptor :
      NumericArrayDescriptor

    degreeRows :
      List DegreeRowABI

    laplacianMethod :
      Rebuild.SignedLaplacianMethodTag

    laplacianReceipt :
      ReceiptIdBinding

    laplacianGraphVersion :
      GraphVersionBinding

    laplacianParityHash :
      ParityHashBinding

    laplacianABISound :
      Bool

    candidateLaplacianMaterialization :
      Bool

    supportAuthority :
      Bool

open LaplacianABI public

laplacianABICandidateOnly :
  ∀ abi →
  laplacianABISound abi ≡ true →
  candidateLaplacianMaterialization abi ≡ true →
  supportAuthority abi ≡ false →
  Set
laplacianABICandidateOnly _ _ _ _ =
  Structure.FormalStructureAuthorityBoundary

------------------------------------------------------------------------
-- Eigenvector / spectral coordinate ABI.

record EigenCoordinateABI : Set where
  constructor eigenCoordinateABI
  field
    eigenvalueDescriptor :
      NumericArrayDescriptor

    eigenvectorDescriptor :
      NumericArrayDescriptor

    coordinateDescriptor :
      NumericArrayDescriptor

    coordinateRows :
      List Rebuild.SpectralCoordinateMapRow

    coordinateRowMap :
      List RowMapBinding

    coordinateMethod :
      Vector.EmbeddingMethodTag

    coordinateLaplacian :
      LaplacianABI

    coordinateReceipt :
      ReceiptIdBinding

    coordinateGraphVersion :
      GraphVersionBinding

    coordinateParityHash :
      ParityHashBinding

    eigenEquationWitnessSupplied :
      Bool

    coordinateRowsMatchWitness :
      Bool

    eigenCoordSound :
      Bool

    candidateVectorCoordinateMaterialization :
      Bool

    vectorAuthority :
      Bool

    evidenceSupportAuthority :
      Bool

open EigenCoordinateABI public

eigenCoordinateABICandidateOnly :
  ∀ abi →
  eigenCoordSound abi ≡ true →
  candidateVectorCoordinateMaterialization abi ≡ true →
  vectorAuthority abi ≡ false →
  evidenceSupportAuthority abi ≡ false →
  Set
eigenCoordinateABICandidateOnly _ _ _ _ _ =
  Structure.FormalStructureAuthorityBoundary

------------------------------------------------------------------------
-- GEMV runtime payload.

record GEMVPayloadABI : Set where
  constructor gemvPayloadABI
  field
    matrixADescriptor :
      NumericArrayDescriptor

    vectorZDescriptor :
      NumericArrayDescriptor

    vectorBDescriptor :
      NumericArrayDescriptor

    gemvRowMap :
      List RowMapBinding

    gemvReceiptIds :
      List ReceiptIdBinding

    gemvGraphVersion :
      GraphVersionBinding

    gemvParityHash :
      ParityHashBinding

    gemvBound :
      Bool

    payloadIntegrityCandidate :
      Bool

    semanticAuthority :
      Bool

    runtimeAuthority :
      Bool

open GEMVPayloadABI public

gemvPayloadCandidateOnly :
  ∀ payload →
  gemvBound payload ≡ true →
  payloadIntegrityCandidate payload ≡ true →
  semanticAuthority payload ≡ false →
  runtimeAuthority payload ≡ false →
  Set
gemvPayloadCandidateOnly _ _ _ _ _ =
  Structure.FormalStructureAuthorityBoundary

------------------------------------------------------------------------
-- Rebuildability and admission.

record PNFSpectralNumericRebuildWitness : Set where
  constructor pnfSpectralNumericRebuildWitness
  field
    registryRows :
      List Registry.ObjectRegistryRow

    residualEdgeRows :
      List ResidualEdgeTableRow

    adjacencyABI :
      SignedAdjacencyABI

    degreeABI :
      List DegreeRowABI

    laplacianABIWitness :
      LaplacianABI

    coordinateABI :
      EigenCoordinateABI

    gemvABI :
      GEMVPayloadABI

    coordinateRebuildabilityWitness :
      Rebuild.CoordinateRebuildabilityWitness

    registryBound :
      Bool

    edgeTableBound :
      Bool

    adjacencyBound :
      Bool

    laplacianBound :
      Bool

    coordinateBound :
      Bool

    parityHashBound :
      Bool

    rebuildable :
      Bool

    candidateMaterialization :
      Bool

    semanticAuthority :
      Bool

open PNFSpectralNumericRebuildWitness public

rebuildableCandidateOnly :
  ∀ witness →
  rebuildable witness ≡ true →
  candidateMaterialization witness ≡ true →
  semanticAuthority witness ≡ false →
  Set
rebuildableCandidateOnly _ _ _ _ =
  Structure.FormalStructureAuthorityBoundary

record NumericPayloadAdmissionRule : Set where
  constructor numericPayloadAdmissionRule
  field
    rebuildWitness :
      PNFSpectralNumericRebuildWitness

    schemaValid :
      Bool

    registryBoundForAdmission :
      Bool

    graphVersionBound :
      Bool

    receiptCoverage :
      Bool

    parityHashBoundForAdmission :
      Bool

    rebuildableForAdmission :
      Bool

    admitNumericPayload :
      Bool

    candidateRuntimeArtifact :
      Bool

    semanticAuthorityPromoted :
      Bool

    evidenceAuthorityPromoted :
      Bool

    tradingAuthorityPromoted :
      Bool

    securityAuthorityPromoted :
      Bool

    runtimeDeploymentAuthorityPromoted :
      Bool

open NumericPayloadAdmissionRule public

admittedPayloadCandidateOnly :
  ∀ rule →
  admitNumericPayload rule ≡ true →
  candidateRuntimeArtifact rule ≡ true →
  semanticAuthorityPromoted rule ≡ false →
  evidenceAuthorityPromoted rule ≡ false →
  tradingAuthorityPromoted rule ≡ false →
  securityAuthorityPromoted rule ≡ false →
  runtimeDeploymentAuthorityPromoted rule ≡ false →
  Set
admittedPayloadCandidateOnly _ _ _ _ _ _ _ _ =
  Structure.FormalStructureAuthorityBoundary

admissionRequiresSchema :
  ∀ rule →
  admitNumericPayload rule ≡ true →
  schemaValid rule ≡ true →
  Set
admissionRequiresSchema _ _ _ =
  Structure.FormalStructureLawKind

admissionRequiresRebuildability :
  ∀ rule →
  admitNumericPayload rule ≡ true →
  rebuildableForAdmission rule ≡ true →
  Set
admissionRequiresRebuildability _ _ _ =
  Structure.FormalStructureLawKind

------------------------------------------------------------------------
-- Symbolic-relational bridge and authority impossibility.

record SymbolicPNFNumericMaterialization : Set where
  constructor symbolicPNFNumericMaterialization
  field
    symbolicObjects :
      List Core.PredicateObjectRef

    symbolicResidualEdges :
      List Graph.PNFGraphEdge

    symbolicWeightedGraph :
      Graph.WeightedPNFGraph

    numericPayload :
      PNFSpectralNumericRebuildWitness

    admission :
      NumericPayloadAdmissionRule

    materializesSymbolicPNF :
      Bool

    materializationIsCandidate :
      Bool

    semanticTruth :
      Bool

    admissibleEvidenceAuthority :
      Bool

    runtimeAuthority :
      Bool

open SymbolicPNFNumericMaterialization public

materializationCandidateOnly :
  ∀ bridge →
  materializesSymbolicPNF bridge ≡ true →
  materializationIsCandidate bridge ≡ true →
  semanticTruth bridge ≡ false →
  admissibleEvidenceAuthority bridge ≡ false →
  runtimeAuthority bridge ≡ false →
  Set
materializationCandidateOnly _ _ _ _ _ _ =
  Structure.FormalStructureAuthorityBoundary

data NumericPayloadPromotion : Set where

numericPayloadPromotionImpossible :
  NumericPayloadPromotion →
  ⊥
numericPayloadPromotionImpossible ()

numericArraysDoNotCreateAuthority : String
numericArraysDoNotCreateAuthority =
  "Numeric ABI payloads only materialize an already typed symbolic PNF graph under row-map, receipt, graph-version, parity-hash, and rebuildability witnesses. Arrays, GEMV outputs, Laplacian rows, eigenvectors, vector proximity, and parity hashes do not create semantic, evidence, trading, security, legal, clinical, or deployment authority."

