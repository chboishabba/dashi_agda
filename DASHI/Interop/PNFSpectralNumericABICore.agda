module DASHI.Interop.PNFSpectralNumericABICore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Core.AuthorityBoundary as Boundary
import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Core.FormalStructureLawCore as Formal
import DASHI.Interop.PNFSpectralCoordinateRebuildability as Rebuild
import DASHI.Interop.PNFSpectralFieldGraph as Graph
import DASHI.Interop.PNFSpectralVectorIndex as Vector
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.SpectralOperatorShapeCore as ShapeCore

------------------------------------------------------------------------
-- PNF spectral numeric ABI core.
--
-- This module is a structural candidate surface for runtime numeric ABI
-- materialization.  It binds the PNF spectral row map, residual edge table,
-- adjacency, Laplacian, spectral coordinate, GEMV payload, rebuild witness,
-- and admission / authority boundaries without promoting runtime numeric
-- values, truth, support, admissibility, or authority.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data PNFSpectralNumericABIStatus : Set where
  pnfSpectralNumericABICandidateOnlyNoRuntimePromotion :
    PNFSpectralNumericABIStatus

data PNFSpectralNumericABIComponent : Set where
  rowMapBindingComponent :
    PNFSpectralNumericABIComponent

  residualEdgeTableComponent :
    PNFSpectralNumericABIComponent

  adjacencyABIComponent :
    PNFSpectralNumericABIComponent

  laplacianABIComponent :
    PNFSpectralNumericABIComponent

  eigenSpectralCoordinateABIComponent :
    PNFSpectralNumericABIComponent

  gemvPayloadComponent :
    PNFSpectralNumericABIComponent

  rebuildWitnessComponent :
    PNFSpectralNumericABIComponent

  admissionRuleComponent :
    PNFSpectralNumericABIComponent

  authorityBoundaryLemmaComponent :
    PNFSpectralNumericABIComponent

  formalStructureBoundaryComponent :
    PNFSpectralNumericABIComponent

canonicalPNFSpectralNumericABIComponents :
  List PNFSpectralNumericABIComponent
canonicalPNFSpectralNumericABIComponents =
  rowMapBindingComponent
  ∷ residualEdgeTableComponent
  ∷ adjacencyABIComponent
  ∷ laplacianABIComponent
  ∷ eigenSpectralCoordinateABIComponent
  ∷ gemvPayloadComponent
  ∷ rebuildWitnessComponent
  ∷ admissionRuleComponent
  ∷ authorityBoundaryLemmaComponent
  ∷ formalStructureBoundaryComponent
  ∷ []

pnfSpectralNumericABIStatement : String
pnfSpectralNumericABIStatement =
  "PNF spectral numeric ABI surfaces remain candidate-only. Row-map binding, residual edges, adjacency, Laplacian, spectral coordinates, GEMV payloads, and rebuild witnesses are materialized as typed structural records; they do not promote truth, support, admissibility, or runtime authority."

pnfSpectralNumericABIBoundaryStatement : String
pnfSpectralNumericABIBoundaryStatement =
  "The numeric ABI is a fail-closed intake surface only. Candidate-only rows, citation/no-artifact boundaries, and formal authority boundaries remain false until a separate promotion artifact exists."

data PNFSpectralNumericABIPromotion : Set where

pnfSpectralNumericABIPromotionImpossible :
  PNFSpectralNumericABIPromotion →
  ⊥
pnfSpectralNumericABIPromotionImpossible ()

------------------------------------------------------------------------
-- Row-map binding.

record PNFRowMapBinding : Set where
  constructor pnfRowMapBinding
  field
    rowMapLabel :
      String

    rowMapOwner :
      String

    rowMapSurface :
      String

    rowMap :
      Rebuild.SpectralCoordinateMapRow

    rowMapIsCanonical :
      rowMap ≡ Rebuild.canonicalSpectralCoordinateMapRow

    rowMapWitness :
      Rebuild.CoordinateRebuildabilityWitness

    rowMapWitnessIsCanonical :
      rowMapWitness ≡ Rebuild.canonicalRebuildabilityWitness

    rowMapRegistryPayload :
      Rebuild.RegistryPayload

    rowMapRegistryPayloadIsCanonical :
      rowMapRegistryPayload ≡ Rebuild.canonicalRegistryPayload

    rowMapCoordinate :
      Vector.VectorCoordinate

    rowMapCoordinateIsWitnessCoordinate :
      rowMapCoordinate ≡ Rebuild.coordinate rowMapWitness

    rowMapCandidateOnly :
      Bool

    rowMapCandidateOnlyIsTrue :
      rowMapCandidateOnly ≡ true

    rowMapTruthAuthority :
      Bool

    rowMapTruthAuthorityIsFalse :
      rowMapTruthAuthority ≡ false

    rowMapSupportAuthority :
      Bool

    rowMapSupportAuthorityIsFalse :
      rowMapSupportAuthority ≡ false

    rowMapAdmissibilityAuthority :
      Bool

    rowMapAdmissibilityAuthorityIsFalse :
      rowMapAdmissibilityAuthority ≡ false

    rowMapRuntimeAuthority :
      Bool

    rowMapRuntimeAuthorityIsFalse :
      rowMapRuntimeAuthority ≡ false

    rowMapPromoted :
      Bool

    rowMapPromotedIsFalse :
      rowMapPromoted ≡ false

open PNFRowMapBinding public

canonicalPNFRowMapBinding :
  PNFRowMapBinding
canonicalPNFRowMapBinding =
  pnfRowMapBinding
    "pnf row-map binding"
    "DASHI.Interop.PNFSpectralNumericABICore"
    "row-map materialization for a rebuildable spectral coordinate"
    Rebuild.canonicalSpectralCoordinateMapRow
    refl
    Rebuild.canonicalRebuildabilityWitness
    refl
    Rebuild.canonicalRegistryPayload
    refl
    (Rebuild.coordinate Rebuild.canonicalRebuildabilityWitness)
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalPNFRowMapBindingIsCanonical :
  rowMap canonicalPNFRowMapBinding ≡ Rebuild.canonicalSpectralCoordinateMapRow
canonicalPNFRowMapBindingIsCanonical =
  refl

------------------------------------------------------------------------
-- Residual edge table ABI.

record PNFResidualEdgeTableRow : Set where
  constructor pnfResidualEdgeTableRow
  field
    residualEdgeSource :
      Graph.PNFGraphVertex

    residualEdgeTarget :
      Graph.PNFGraphVertex

    residualEdgeLevel :
      Residual.ResidualLevel

    residualEdgeSignedWeight :
      Graph.SignedResidualWeight

    residualEdgeSignedWeightIsResidual :
      residualEdgeSignedWeight
      ≡
      Graph.residualSignedWeight residualEdgeLevel

    residualEdgeCandidateOnly :
      Bool

    residualEdgeCandidateOnlyIsTrue :
      residualEdgeCandidateOnly ≡ true

    residualEdgeTruthAuthority :
      Bool

    residualEdgeTruthAuthorityIsFalse :
      residualEdgeTruthAuthority ≡ false

    residualEdgeSupportAuthority :
      Bool

    residualEdgeSupportAuthorityIsFalse :
      residualEdgeSupportAuthority ≡ false

    residualEdgeAdmissibilityAuthority :
      Bool

    residualEdgeAdmissibilityAuthorityIsFalse :
      residualEdgeAdmissibilityAuthority ≡ false

    residualEdgeRuntimeAuthority :
      Bool

    residualEdgeRuntimeAuthorityIsFalse :
      residualEdgeRuntimeAuthority ≡ false

open PNFResidualEdgeTableRow public

canonicalPNFResidualEdgeTableRow :
  PNFResidualEdgeTableRow
canonicalPNFResidualEdgeTableRow =
  pnfResidualEdgeTableRow
    (Rebuild.adjacencySource Rebuild.canonicalSignedAdjacencyRow)
    (Rebuild.adjacencyTarget Rebuild.canonicalSignedAdjacencyRow)
    (Rebuild.residualLevel Rebuild.canonicalSignedAdjacencyRow)
    (Rebuild.signedWeight Rebuild.canonicalSignedAdjacencyRow)
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

record PNFResidualEdgeTableABI : Set where
  constructor pnfResidualEdgeTableABI
  field
    residualEdgeTableLabel :
      String

    residualEdgeTableOwner :
      String

    residualEdgeTableSurface :
      String

    residualEdgeTableRows :
      List PNFResidualEdgeTableRow

    residualEdgeTableRowCount :
      Nat

    residualEdgeTableRowCountIsCanonical :
      residualEdgeTableRowCount ≡ listCount residualEdgeTableRows

    residualEdgeTableCandidateOnly :
      Bool

    residualEdgeTableCandidateOnlyIsTrue :
      residualEdgeTableCandidateOnly ≡ true

    residualEdgeTablePromoted :
      Bool

    residualEdgeTablePromotedIsFalse :
      residualEdgeTablePromoted ≡ false

    residualEdgeTableTruthAuthority :
      Bool

    residualEdgeTableTruthAuthorityIsFalse :
      residualEdgeTableTruthAuthority ≡ false

    residualEdgeTableSupportAuthority :
      Bool

    residualEdgeTableSupportAuthorityIsFalse :
      residualEdgeTableSupportAuthority ≡ false

    residualEdgeTableAdmissibilityAuthority :
      Bool

    residualEdgeTableAdmissibilityAuthorityIsFalse :
      residualEdgeTableAdmissibilityAuthority ≡ false

    residualEdgeTableRuntimeAuthority :
      Bool

    residualEdgeTableRuntimeAuthorityIsFalse :
      residualEdgeTableRuntimeAuthority ≡ false

    residualEdgeTableStatement :
      String

open PNFResidualEdgeTableABI public

canonicalPNFResidualEdgeTableABI :
  PNFResidualEdgeTableABI
canonicalPNFResidualEdgeTableABI =
  pnfResidualEdgeTableABI
    "pnf residual edge table ABI"
    "DASHI.Interop.PNFSpectralNumericABICore"
    "residual edge table materialization for signed adjacency rows"
    (canonicalPNFResidualEdgeTableRow ∷ [])
    1
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "Residual edge rows are candidate rows only; they are not runtime truth or support."

------------------------------------------------------------------------
-- Adjacency ABI.

record PNFAdjacencyABI : Set where
  constructor pnfAdjacencyABI
  field
    adjacencyLabel :
      String

    adjacencyOwner :
      String

    adjacencySurface :
      String

    adjacencyRows :
      List Rebuild.SignedAdjacencyRow

    adjacencyRowCount :
      Nat

    adjacencyRowCountIsCanonical :
      adjacencyRowCount ≡ listCount adjacencyRows

    adjacencyDegreeRows :
      List Rebuild.AbsoluteDegreeOperatorRow

    adjacencyDegreeRowCount :
      Nat

    adjacencyDegreeRowCountIsCanonical :
      adjacencyDegreeRowCount ≡ listCount adjacencyDegreeRows

    adjacencyRowMapBinding :
      PNFRowMapBinding

    adjacencyRowMapBindingIsCanonical :
      adjacencyRowMapBinding ≡ canonicalPNFRowMapBinding

    adjacencyCandidateOnly :
      Bool

    adjacencyCandidateOnlyIsTrue :
      adjacencyCandidateOnly ≡ true

    adjacencyTruthAuthority :
      Bool

    adjacencyTruthAuthorityIsFalse :
      adjacencyTruthAuthority ≡ false

    adjacencySupportAuthority :
      Bool

    adjacencySupportAuthorityIsFalse :
      adjacencySupportAuthority ≡ false

    adjacencyAdmissibilityAuthority :
      Bool

    adjacencyAdmissibilityAuthorityIsFalse :
      adjacencyAdmissibilityAuthority ≡ false

    adjacencyRuntimeAuthority :
      Bool

    adjacencyRuntimeAuthorityIsFalse :
      adjacencyRuntimeAuthority ≡ false

    adjacencyStatement :
      String

open PNFAdjacencyABI public

canonicalPNFAdjacencyABI :
  PNFAdjacencyABI
canonicalPNFAdjacencyABI =
  pnfAdjacencyABI
    "pnf adjacency ABI"
    "DASHI.Interop.PNFSpectralNumericABICore"
    "signed adjacency and absolute-degree materialization"
    (Rebuild.canonicalSignedAdjacencyRow ∷ [])
    1
    refl
    (Rebuild.canonicalAbsoluteDegreeOperatorRow ∷ [])
    1
    refl
    canonicalPNFRowMapBinding
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "Adjacency is a candidate materialization surface only."

------------------------------------------------------------------------
-- Laplacian ABI.

record PNFLaplacianABI : Set where
  constructor pnfLaplacianABI
  field
    laplacianLabel :
      String

    laplacianSurface :
      String

    laplacianReceipt :
      ShapeCore.SpectralOperatorShapeReceipt

    laplacianReceiptIsCanonical :
      laplacianReceipt ≡ ShapeCore.canonicalSignedResidualLaplacianReceipt

    laplacianSignedResidualFirstLayer :
      Bool

    laplacianSignedResidualFirstLayerIsTrue :
      laplacianSignedResidualFirstLayer ≡ true

    laplacianHigherHodgeDiagnosticOnly :
      Bool

    laplacianHigherHodgeDiagnosticOnlyIsTrue :
      laplacianHigherHodgeDiagnosticOnly ≡ true

    laplacianSemanticTruthPromotion :
      Bool

    laplacianSemanticTruthPromotionIsFalse :
      laplacianSemanticTruthPromotion ≡ false

    laplacianRuntimeEvidencePromotion :
      Bool

    laplacianRuntimeEvidencePromotionIsFalse :
      laplacianRuntimeEvidencePromotion ≡ false

    laplacianContinuumSpectralPromotion :
      Bool

    laplacianContinuumSpectralPromotionIsFalse :
      laplacianContinuumSpectralPromotion ≡ false

    laplacianStatement :
      String

open PNFLaplacianABI public

canonicalPNFLaplacianABI :
  PNFLaplacianABI
canonicalPNFLaplacianABI =
  pnfLaplacianABI
    "pnf Laplacian ABI"
    "DASHI.Interop.PNFSpectralNumericABICore"
    ShapeCore.canonicalSignedResidualLaplacianReceipt
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    "Signed residual graph Laplacian is the first implementable layer; richer Hodge layers remain diagnostic-only."

------------------------------------------------------------------------
-- Rebuild witness and eigen/spectral coordinate ABI.

record PNFRebuildWitness : Set where
  constructor pnfRebuildWitness
  field
    rebuildabilityWitness :
      Rebuild.CoordinateRebuildabilityWitness

    rebuildabilityWitnessIsCanonical :
      rebuildabilityWitness ≡ Rebuild.canonicalRebuildabilityWitness

    rebuildRegistryPayload :
      Rebuild.RegistryPayload

    rebuildRegistryPayloadIsCanonical :
      rebuildRegistryPayload ≡ Rebuild.canonicalRegistryPayload

    rebuildCoordinate :
      Vector.VectorCoordinate

    rebuildCoordinateIsRebuilt :
      rebuildCoordinate ≡ Rebuild.coordinate rebuildabilityWitness

    rebuildable :
      Bool

    rebuildableIsTrue :
      rebuildable ≡ true

    registryPayloadAuthority :
      Bool

    registryPayloadAuthorityIsTrue :
      registryPayloadAuthority ≡ true

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

open PNFRebuildWitness public

canonicalPNFRebuildWitness :
  PNFRebuildWitness
canonicalPNFRebuildWitness =
  pnfRebuildWitness
    Rebuild.canonicalRebuildabilityWitness
    refl
    Rebuild.canonicalRegistryPayload
    refl
    (Rebuild.coordinate Rebuild.canonicalRebuildabilityWitness)
    refl
    true
    refl
    true
    refl
    false
    refl

record PNFEigenSpectralCoordinateABI : Set where
  constructor pnfEigenSpectralCoordinateABI
  field
    spectralLabel :
      String

    spectralOwner :
      String

    spectralSurface :
      String

    spectralMethod :
      Vector.EmbeddingMethodTag

    spectralMethodIsCanonical :
      spectralMethod ≡ Vector.pnfSpectralLaplacianV1

    spectralCoordinate :
      Vector.VectorCoordinate

    spectralCoordinateIsCanonical :
      spectralCoordinate ≡ Vector.canonicalSampleCoordinate

    spectralObject :
      Vector.ObjectRef

    spectralObjectIsCanonical :
      spectralObject ≡ Vector.canonicalSampleObject

    spectralVectorRow :
      Vector.VectorIndexRow

    spectralVectorRowIsCanonical :
      spectralVectorRow ≡ Vector.canonicalSampleRow

    spectralCoordinateRow :
      Rebuild.SpectralCoordinateMapRow

    spectralCoordinateRowIsCanonical :
      spectralCoordinateRow ≡ Rebuild.canonicalSpectralCoordinateMapRow

    spectralWitness :
      PNFRebuildWitness

    spectralWitnessIsCanonical :
      spectralWitness ≡ canonicalPNFRebuildWitness

    spectralCandidateOnly :
      Bool

    spectralCandidateOnlyIsTrue :
      spectralCandidateOnly ≡ true

    spectralTruthAuthority :
      Bool

    spectralTruthAuthorityIsFalse :
      spectralTruthAuthority ≡ false

    spectralSupportAuthority :
      Bool

    spectralSupportAuthorityIsFalse :
      spectralSupportAuthority ≡ false

    spectralAdmissibilityAuthority :
      Bool

    spectralAdmissibilityAuthorityIsFalse :
      spectralAdmissibilityAuthority ≡ false

    spectralStatement :
      String

open PNFEigenSpectralCoordinateABI public

canonicalPNFEigenSpectralCoordinateABI :
  PNFEigenSpectralCoordinateABI
canonicalPNFEigenSpectralCoordinateABI =
  pnfEigenSpectralCoordinateABI
    "pnf eigen-spectral coordinate ABI"
    "DASHI.Interop.PNFSpectralNumericABICore"
    "spectral coordinate materialization from a rebuild witness"
    Vector.pnfSpectralLaplacianV1
    refl
    Vector.canonicalSampleCoordinate
    refl
    Vector.canonicalSampleObject
    refl
    Vector.canonicalSampleRow
    refl
    Rebuild.canonicalSpectralCoordinateMapRow
    refl
    canonicalPNFRebuildWitness
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    "Eigen/spectral coordinates are candidate-only ABI rows."

------------------------------------------------------------------------
-- GEMV payload.

record PNFGEMVPayload : Set where
  constructor pnfGEMVPayload
  field
    gemvLabel :
      String

    gemvOwner :
      String

    gemvSurface :
      String

    gemvInputVectorRow :
      Vector.VectorIndexRow

    gemvInputVectorRowIsCanonical :
      gemvInputVectorRow ≡ Vector.canonicalSampleRow

    gemvInputCandidate :
      Vector.CandidateRef

    gemvInputCandidateIsCanonical :
      gemvInputCandidate ≡ Vector.canonicalSampleCandidate

    gemvProposalRow :
      Vector.VectorArithmeticProposalRow

    gemvProposalRowIsCanonical :
      gemvProposalRow ≡ Vector.canonicalArithmeticProposalRow

    gemvGraphProximity :
      Vector.PNFGraphOperatorProximity

    gemvGraphProximityIsCanonical :
      gemvGraphProximity ≡ Vector.canonicalGraphOperatorProximity

    gemvCandidateOnly :
      Bool

    gemvCandidateOnlyIsTrue :
      gemvCandidateOnly ≡ true

    gemvTruthAuthority :
      Bool

    gemvTruthAuthorityIsFalse :
      gemvTruthAuthority ≡ false

    gemvSupportAuthority :
      Bool

    gemvSupportAuthorityIsFalse :
      gemvSupportAuthority ≡ false

    gemvAdmissibilityAuthority :
      Bool

    gemvAdmissibilityAuthorityIsFalse :
      gemvAdmissibilityAuthority ≡ false

    gemvRuntimeAuthority :
      Bool

    gemvRuntimeAuthorityIsFalse :
      gemvRuntimeAuthority ≡ false

    gemvStatement :
      String

open PNFGEMVPayload public

gemvDType : String
gemvDType =
  "float32"

gemvRows : Nat
gemvRows =
  1

gemvCols : Nat
gemvCols =
  1

gemvMatrixA : String
gemvMatrixA =
  "runtime field A: matrix payload bound by PNFGEMVPayload"

gemvVectorZ : String
gemvVectorZ =
  "runtime field z: input vector payload bound by PNFGEMVPayload"

gemvVectorB : String
gemvVectorB =
  "runtime field b: output vector payload bound by PNFGEMVPayload"

gemvParityHash : String
gemvParityHash =
  "runtime field parity_hash: integrity candidate bound by PNFGEMVPayload"

canonicalPNFGEMVPayload :
  PNFGEMVPayload
canonicalPNFGEMVPayload =
  pnfGEMVPayload
    "pnf GEMV payload"
    "DASHI.Interop.PNFSpectralNumericABICore"
    "candidate-only GEMV payload over spectral rows"
    Vector.canonicalSampleRow
    refl
    Vector.canonicalSampleCandidate
    refl
    Vector.canonicalArithmeticProposalRow
    refl
    Vector.canonicalGraphOperatorProximity
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "GEMV payload stays in the candidate and proposal lanes."

------------------------------------------------------------------------
-- Admission rule.

record PNFAdmissionRule : Set where
  constructor pnfAdmissionRule
  field
    admissionLabel :
      String

    admissionRow :
      CandidateOnly.CandidateOnlyRow

    admissionReceipt :
      CandidateOnly.CandidateOnlyReceipt admissionRow

    admissionAuthorityBundle :
      AuthorityNA.AuthorityNonPromotionBundle

    admissionFormalBoundary :
      Formal.FormalStructureAuthorityBoundary

    admissionCitationBoundary :
      Boundary.CitationAuthorityNoArtifact

    admissionCandidateOnlyIsTrue :
      CandidateOnly.candidateOnly admissionRow ≡ true

    admissionPromotedIsFalse :
      CandidateOnly.promoted admissionRow ≡ false

    admissionNoTruthAuthority :
      CandidateOnly.carriesTruthAuthority admissionRow ≡ false

    admissionNoSupportAuthority :
      CandidateOnly.carriesSupportAuthority admissionRow ≡ false

    admissionNoAdmissibilityAuthority :
      CandidateOnly.carriesAdmissibilityAuthority admissionRow ≡ false

    admissionNoTradingAuthority :
      CandidateOnly.carriesTradingAuthority admissionRow ≡ false

    admissionNoRuntimeAuthority :
      CandidateOnly.carriesRuntimeAuthority admissionRow ≡ false

    admissionNoTheoremAuthority :
      CandidateOnly.carriesTheoremAuthority admissionRow ≡ false

    admissionAuthorityBundlePromotesAnyAuthority :
      AuthorityNA.promotesAnyAuthority admissionAuthorityBundle ≡ false

    admissionStatement :
      String

open PNFAdmissionRule public

canonicalPNFAdmissionCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalPNFAdmissionCandidateRow =
  CandidateOnly.mkCandidateOnlyRow
    "pnf spectral numeric ABI admission candidate"
    "DASHI.Interop.PNFSpectralNumericABICore"
    "pnf numeric abi admission"
    CandidateOnly.rowCandidateKind
    CandidateOnly.rowCandidateOnlyStatus
    "admission remains candidate-only"
    "promotion requires a separate receipt"

canonicalPNFAdmissionReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalPNFAdmissionCandidateRow
canonicalPNFAdmissionReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalPNFAdmissionCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalPNFAuthorityBundle :
  AuthorityNA.AuthorityNonPromotionBundle
canonicalPNFAuthorityBundle =
  AuthorityNA.mkClosedAuthorityNonPromotionBundle
    "pnf spectral numeric ABI authority bundle"

canonicalPNFAdmissionCitationBoundary :
  Boundary.CitationAuthorityNoArtifact
canonicalPNFAdmissionCitationBoundary =
  record
    { citationBoundary =
        record
          { authorityKind = Boundary.CitationAuthority
          ; authorityKindMatches = refl
          ; recordIdentifier =
              "DASHI.Interop.PNFSpectralNumericABICore"
          ; citation =
              "pnf spectral numeric abi candidate-only citation"
          ; authorityAccepted = true
          ; artifactAuthority = false
          ; machineReadableArtifactPresent = false
          ; notes =
              "candidate-only numeric ABI boundary" ∷ []
          }
    ; citationAuthorityAccepted = refl
    ; artifactAuthorityIsFalse = refl
    ; machineReadableArtifactPresentIsFalse = refl
    }

canonicalPNFAdmissionRule :
  PNFAdmissionRule
canonicalPNFAdmissionRule =
  pnfAdmissionRule
    "pnf spectral numeric ABI admission rule"
    canonicalPNFAdmissionCandidateRow
    canonicalPNFAdmissionReceipt
    canonicalPNFAuthorityBundle
    Formal.canonicalFormalStructureAuthorityBoundary
    canonicalPNFAdmissionCitationBoundary
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    "Admission remains candidate-only and fails closed."

------------------------------------------------------------------------
-- Authority-boundary lemmas.

record PNFAuthorityBoundaryLemmas : Set where
  constructor pnfAuthorityBoundaryLemmas
  field
    formalBoundary :
      Formal.FormalStructureAuthorityBoundary

    formalRepresentationAuthorityIsFalse :
      Formal.FormalStructureAuthorityBoundary.representationAuthority formalBoundary
      ≡
      false

    formalStatisticAuthorityIsFalse :
      Formal.FormalStructureAuthorityBoundary.statisticAuthority formalBoundary
      ≡
      false

    formalProjectionAuthorityIsFalse :
      Formal.FormalStructureAuthorityBoundary.projectionAuthority formalBoundary
      ≡
      false

    formalDigestAuthorityIsFalse :
      Formal.FormalStructureAuthorityBoundary.digestAuthority formalBoundary
      ≡
      false

    formalCoordinateModelAuthorityIsFalse :
      Formal.FormalStructureAuthorityBoundary.coordinateModelAuthority
        formalBoundary
      ≡
      false

    formalSemanticAuthorityIsFalse :
      Formal.FormalStructureAuthorityBoundary.semanticAuthority formalBoundary
      ≡
      false

    formalDomainAuthorityIsFalse :
      Formal.FormalStructureAuthorityBoundary.domainAuthority formalBoundary
      ≡
      false

    citationBoundary :
      Boundary.CitationAuthorityNoArtifact

    citationAuthorityAcceptedIsTrue :
      Boundary.authorityAccepted (Boundary.citationBoundary citationBoundary)
      ≡
      true

    citationArtifactAuthorityIsFalse :
      Boundary.artifactAuthority (Boundary.citationBoundary citationBoundary)
      ≡
      false

    citationMachineReadableArtifactPresentIsFalse :
      Boundary.machineReadableArtifactPresent
        (Boundary.citationBoundary citationBoundary)
      ≡
      false

    authorityBundle :
      AuthorityNA.AuthorityNonPromotionBundle

    authorityBundlePromotesAnyAuthorityIsFalse :
      AuthorityNA.promotesAnyAuthority authorityBundle ≡ false

    authorityKinds :
      List AuthorityNA.AuthorityKind

    authorityKindsAreCanonical :
      authorityKinds ≡ AuthorityNA.canonicalAuthorityKinds

open PNFAuthorityBoundaryLemmas public

canonicalPNFAuthorityBoundaryLemmas :
  PNFAuthorityBoundaryLemmas
canonicalPNFAuthorityBoundaryLemmas =
  pnfAuthorityBoundaryLemmas
    Formal.canonicalFormalStructureAuthorityBoundary
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    canonicalPNFAdmissionCitationBoundary
    refl
    refl
    refl
    canonicalPNFAuthorityBundle
    refl
    AuthorityNA.canonicalAuthorityKinds
    refl

------------------------------------------------------------------------
-- Aggregate numeric ABI receipt.

record PNFSpectralNumericABICoreReceipt : Set where
  constructor pnfSpectralNumericABICoreReceipt
  field
    status :
      PNFSpectralNumericABIStatus

    statusIsCandidateOnly :
      status ≡ pnfSpectralNumericABICandidateOnlyNoRuntimePromotion

    components :
      List PNFSpectralNumericABIComponent

    componentsAreCanonical :
      components ≡ canonicalPNFSpectralNumericABIComponents

    rowMapBinding :
      PNFRowMapBinding

    rowMapBindingIsCanonical :
      rowMapBinding ≡ canonicalPNFRowMapBinding

    residualEdgeTable :
      PNFResidualEdgeTableABI

    residualEdgeTableIsCanonical :
      residualEdgeTable ≡ canonicalPNFResidualEdgeTableABI

    adjacencyABI :
      PNFAdjacencyABI

    adjacencyABIIsCanonical :
      adjacencyABI ≡ canonicalPNFAdjacencyABI

    laplacianABI :
      PNFLaplacianABI

    laplacianABIIsCanonical :
      laplacianABI ≡ canonicalPNFLaplacianABI

    eigenSpectralCoordinateABI :
      PNFEigenSpectralCoordinateABI

    eigenSpectralCoordinateABIIsCanonical :
      eigenSpectralCoordinateABI ≡ canonicalPNFEigenSpectralCoordinateABI

    gemvPayload :
      PNFGEMVPayload

    gemvPayloadIsCanonical :
      gemvPayload ≡ canonicalPNFGEMVPayload

    rebuildWitness :
      PNFRebuildWitness

    rebuildWitnessIsCanonical :
      rebuildWitness ≡ canonicalPNFRebuildWitness

    admissionRule :
      PNFAdmissionRule

    admissionRuleIsCanonical :
      admissionRule ≡ canonicalPNFAdmissionRule

    authorityBoundaryLemmas :
      PNFAuthorityBoundaryLemmas

    authorityBoundaryLemmasIsCanonical :
      authorityBoundaryLemmas ≡ canonicalPNFAuthorityBoundaryLemmas

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ pnfSpectralNumericABIStatement

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ pnfSpectralNumericABIBoundaryStatement

open PNFSpectralNumericABICoreReceipt public

canonicalPNFSpectralNumericABICoreReceipt :
  PNFSpectralNumericABICoreReceipt
canonicalPNFSpectralNumericABICoreReceipt =
  pnfSpectralNumericABICoreReceipt
    pnfSpectralNumericABICandidateOnlyNoRuntimePromotion
    refl
    canonicalPNFSpectralNumericABIComponents
    refl
    canonicalPNFRowMapBinding
    refl
    canonicalPNFResidualEdgeTableABI
    refl
    canonicalPNFAdjacencyABI
    refl
    canonicalPNFLaplacianABI
    refl
    canonicalPNFEigenSpectralCoordinateABI
    refl
    canonicalPNFGEMVPayload
    refl
    canonicalPNFRebuildWitness
    refl
    canonicalPNFAdmissionRule
    refl
    canonicalPNFAuthorityBoundaryLemmas
    refl
    true
    refl
    false
    refl
    pnfSpectralNumericABIStatement
    refl
    pnfSpectralNumericABIBoundaryStatement
    refl

------------------------------------------------------------------------
-- v0.2 compatibility aliases.

spectralSchemaV02 : String
spectralSchemaV02 =
  "itir.pnf.spectral_numeric_abi.v0_2"

graphVersion : String
graphVersion =
  "v0.2"

operatorProfile : String
operatorProfile =
  Vector.graphOperatorProfile Vector.canonicalGraphOperatorProximity

objectRegistry : Rebuild.RegistryPayload
objectRegistry =
  Rebuild.canonicalRegistryPayload

adjacencyTable : PNFAdjacencyABI
adjacencyTable =
  canonicalPNFAdjacencyABI

degreeTable : List Rebuild.AbsoluteDegreeOperatorRow
degreeTable =
  adjacencyDegreeRows canonicalPNFAdjacencyABI

laplacianTable : PNFLaplacianABI
laplacianTable =
  canonicalPNFLaplacianABI

phiTable : PNFEigenSpectralCoordinateABI
phiTable =
  canonicalPNFEigenSpectralCoordinateABI

psiTable : PNFGEMVPayload
psiTable =
  canonicalPNFGEMVPayload

authorityGate : PNFAuthorityBoundaryLemmas
authorityGate =
  canonicalPNFAuthorityBoundaryLemmas

------------------------------------------------------------------------
-- Projection lemmas over the canonical receipt.

canonicalPNFSpectralNumericABICoreReceiptStatusIsCandidateOnly :
  status canonicalPNFSpectralNumericABICoreReceipt
  ≡
  pnfSpectralNumericABICandidateOnlyNoRuntimePromotion
canonicalPNFSpectralNumericABICoreReceiptStatusIsCandidateOnly =
  refl

canonicalPNFSpectralNumericABICoreReceiptCandidateOnlyIsTrue :
  candidateOnly canonicalPNFSpectralNumericABICoreReceipt ≡ true
canonicalPNFSpectralNumericABICoreReceiptCandidateOnlyIsTrue =
  refl

canonicalPNFSpectralNumericABICoreReceiptPromotedIsFalse :
  promoted canonicalPNFSpectralNumericABICoreReceipt ≡ false
canonicalPNFSpectralNumericABICoreReceiptPromotedIsFalse =
  refl

canonicalPNFRowMapBindingCandidateOnlyIsTrue :
  rowMapCandidateOnly canonicalPNFRowMapBinding ≡ true
canonicalPNFRowMapBindingCandidateOnlyIsTrue =
  refl

canonicalPNFResidualEdgeTableCandidateOnlyIsTrue :
  residualEdgeTableCandidateOnly canonicalPNFResidualEdgeTableABI ≡ true
canonicalPNFResidualEdgeTableCandidateOnlyIsTrue =
  refl

canonicalPNFAdjacencyABICandidateOnlyIsTrue :
  adjacencyCandidateOnly canonicalPNFAdjacencyABI ≡ true
canonicalPNFAdjacencyABICandidateOnlyIsTrue =
  refl

canonicalPNFLaplacianABISemanticTruthPromotionIsFalse :
  laplacianSemanticTruthPromotion canonicalPNFLaplacianABI ≡ false
canonicalPNFLaplacianABISemanticTruthPromotionIsFalse =
  refl

canonicalPNFEigenSpectralCoordinateABICandidateOnlyIsTrue :
  spectralCandidateOnly canonicalPNFEigenSpectralCoordinateABI ≡ true
canonicalPNFEigenSpectralCoordinateABICandidateOnlyIsTrue =
  refl

canonicalPNFGEMVPayloadCandidateOnlyIsTrue :
  gemvCandidateOnly canonicalPNFGEMVPayload ≡ true
canonicalPNFGEMVPayloadCandidateOnlyIsTrue =
  refl

canonicalPNFAdmissionRuleCandidateOnlyIsTrue :
  CandidateOnly.candidateOnly (admissionRow canonicalPNFAdmissionRule) ≡ true
canonicalPNFAdmissionRuleCandidateOnlyIsTrue =
  refl

canonicalPNFAuthorityBoundaryLemmaPromotesAnyAuthorityIsFalse :
  AuthorityNA.promotesAnyAuthority
    (authorityBundle canonicalPNFAuthorityBoundaryLemmas)
  ≡
  false
canonicalPNFAuthorityBoundaryLemmaPromotesAnyAuthorityIsFalse =
  refl
