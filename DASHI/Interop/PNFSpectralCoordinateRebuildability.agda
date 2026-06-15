module DASHI.Interop.PNFSpectralCoordinateRebuildability where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Interop.PNFSpectralFieldCore as Core
import DASHI.Interop.PNFSpectralFieldGraph as Graph
import DASHI.Interop.PNFSpectralVectorIndex as Vector
import DASHI.Interop.SensibLawResidualLattice as Residual
import UFTC_Lattice as UFTC

------------------------------------------------------------------------
-- Coordinate rebuildability surface for PNF spectral rows.
--
-- This module records the boundary between rebuildable finite spectral
-- coordinates and text fallback rendering.  A coordinate row is admissible for
-- registry use only when the stored coordinate is definitionally rebuilt from
-- a typed registry payload.  Text fallback rows are renderable labels only, and
-- vector / embedding rows remain non-authoritative proposal carriers.

data CoordinateRebuildabilityStatus : Set where
  checkedCoordinateRebuildability_noTextPromotion :
    CoordinateRebuildabilityStatus

data CoordinateReceiptComponent : Set where
  signedAdjacencyRowsComponent :
    CoordinateReceiptComponent

  absoluteDegreeRowsComponent :
    CoordinateReceiptComponent

  signedLaplacianMethodTagsComponent :
    CoordinateReceiptComponent

  spectralCoordinateMapRowsComponent :
    CoordinateReceiptComponent

  textualFallbackRowsComponent :
    CoordinateReceiptComponent

  embeddingMethodDistinctionComponent :
    CoordinateReceiptComponent

  rebuildabilityWitnessComponent :
    CoordinateReceiptComponent

  inadmissibleNonRebuildableRowsComponent :
    CoordinateReceiptComponent

  vectorNonAuthorityGatesComponent :
    CoordinateReceiptComponent

canonicalCoordinateReceiptComponents :
  List CoordinateReceiptComponent
canonicalCoordinateReceiptComponents =
  signedAdjacencyRowsComponent
  ∷ absoluteDegreeRowsComponent
  ∷ signedLaplacianMethodTagsComponent
  ∷ spectralCoordinateMapRowsComponent
  ∷ textualFallbackRowsComponent
  ∷ embeddingMethodDistinctionComponent
  ∷ rebuildabilityWitnessComponent
  ∷ inadmissibleNonRebuildableRowsComponent
  ∷ vectorNonAuthorityGatesComponent
  ∷ []

------------------------------------------------------------------------
-- Signed adjacency rows and absolute-degree rows.

data AdjacencyRowKind : Set where
  residualSignedAdjacencyRow :
    AdjacencyRowKind

  textualFallbackAdjacencyRow :
    AdjacencyRowKind

record SignedAdjacencyRow : Set where
  constructor signedAdjacencyRow
  field
    adjacencyKind :
      AdjacencyRowKind

    adjacencySource :
      Graph.PNFGraphVertex

    adjacencyTarget :
      Graph.PNFGraphVertex

    residualLevel :
      Residual.ResidualLevel

    signedWeight :
      Graph.SignedResidualWeight

    signedWeightIsResidual :
      signedWeight ≡ Graph.residualSignedWeight residualLevel

    rowCarriesSignedBoundary :
      Bool

    rowCarriesTruth :
      Bool

    rowCarriesAuthority :
      Bool

open SignedAdjacencyRow public

mkSignedAdjacencyRow :
  Graph.PNFGraphVertex →
  Graph.PNFGraphVertex →
  Residual.ResidualLevel →
  SignedAdjacencyRow
mkSignedAdjacencyRow source target residual =
  signedAdjacencyRow
    residualSignedAdjacencyRow
    source
    target
    residual
    (Graph.residualSignedWeight residual)
    refl
    true
    false
    false

record AbsoluteDegreeOperatorRow : Set where
  constructor absoluteDegreeOperatorRow
  field
    degreeVertex :
      Graph.PNFGraphVertex

    rowSignedAdjacency :
      SignedAdjacencyRow

    absoluteDegree :
      UFTC.Severity

    absoluteDegreeIsMagnitude :
      absoluteDegree ≡ Graph.magnitude (signedWeight rowSignedAdjacency)

    absoluteDegreeIgnoresResidualSign :
      Bool

    absoluteDegreePromotesTruth :
      Bool

open AbsoluteDegreeOperatorRow public

mkAbsoluteDegreeOperatorRow :
  SignedAdjacencyRow →
  AbsoluteDegreeOperatorRow
mkAbsoluteDegreeOperatorRow row =
  absoluteDegreeOperatorRow
    (adjacencySource row)
    row
    (Graph.magnitude (signedWeight row))
    refl
    true
    false

canonicalSignedAdjacencyRow :
  SignedAdjacencyRow
canonicalSignedAdjacencyRow =
  mkSignedAdjacencyRow
    (Graph.pnfGraphVertex zero)
    (Graph.pnfGraphVertex (suc zero))
    Residual.contradiction

canonicalAbsoluteDegreeOperatorRow :
  AbsoluteDegreeOperatorRow
canonicalAbsoluteDegreeOperatorRow =
  mkAbsoluteDegreeOperatorRow canonicalSignedAdjacencyRow

canonicalSignedAdjacencyRowIsNegative :
  Graph.sign (signedWeight canonicalSignedAdjacencyRow)
  ≡
  Graph.negativeResidualWeight
canonicalSignedAdjacencyRowIsNegative =
  refl

canonicalAbsoluteDegreeIsNine :
  absoluteDegree canonicalAbsoluteDegreeOperatorRow ≡ 9
canonicalAbsoluteDegreeIsNine =
  refl

canonicalAbsoluteDegreeDoesNotPromoteTruth :
  absoluteDegreePromotesTruth canonicalAbsoluteDegreeOperatorRow ≡ false
canonicalAbsoluteDegreeDoesNotPromoteTruth =
  refl

------------------------------------------------------------------------
-- Signed Laplacian method tags and embedding-method distinction.

data SignedLaplacianMethodTag : Set where
  unsignedResidualGraphLaplacian :
    SignedLaplacianMethodTag

  signedContradictionResidualLaplacian :
    SignedLaplacianMethodTag

  absoluteDegreeSignedResidualLaplacian :
    SignedLaplacianMethodTag

canonicalSignedLaplacianMethods :
  List SignedLaplacianMethodTag
canonicalSignedLaplacianMethods =
  unsignedResidualGraphLaplacian
  ∷ signedContradictionResidualLaplacian
  ∷ absoluteDegreeSignedResidualLaplacian
  ∷ []

data CoordinateEmbeddingLane : Set where
  finiteSpectralCoordinateLane :
    CoordinateEmbeddingLane

  textualFallbackRenderingLane :
    CoordinateEmbeddingLane

  vectorProposalLane :
    CoordinateEmbeddingLane

record EmbeddingMethodDistinction : Set where
  constructor embeddingMethodDistinction
  field
    vectorMethod :
      Vector.EmbeddingMethodTag

    coordinateLane :
      CoordinateEmbeddingLane

    signedMethod :
      SignedLaplacianMethodTag

    methodRebuildableFromRegistry :
      Bool

    methodUsesTextFallback :
      Bool

    methodCarriesAuthority :
      Bool

open EmbeddingMethodDistinction public

canonicalSpectralMethodDistinction :
  EmbeddingMethodDistinction
canonicalSpectralMethodDistinction =
  embeddingMethodDistinction
    Vector.signedResidualLaplacianV1
    finiteSpectralCoordinateLane
    signedContradictionResidualLaplacian
    true
    false
    false

canonicalTextFallbackMethodDistinction :
  EmbeddingMethodDistinction
canonicalTextFallbackMethodDistinction =
  embeddingMethodDistinction
    Vector.textEmbeddingV1
    textualFallbackRenderingLane
    unsignedResidualGraphLaplacian
    false
    true
    false

canonicalSpectralMethodRebuildable :
  methodRebuildableFromRegistry canonicalSpectralMethodDistinction ≡ true
canonicalSpectralMethodRebuildable =
  refl

canonicalTextFallbackMethodNotRebuildable :
  methodRebuildableFromRegistry canonicalTextFallbackMethodDistinction ≡ false
canonicalTextFallbackMethodNotRebuildable =
  refl

------------------------------------------------------------------------
-- Registry payloads and rebuildability witness coordinate = F(payload).

record RegistryPayload : Set where
  constructor registryPayload
  field
    payloadObject :
      Core.PredicateObjectRef

    payloadVertex :
      Graph.PNFGraphVertex

    payloadAdjacency :
      SignedAdjacencyRow

    payloadDegree :
      AbsoluteDegreeOperatorRow

    payloadMethod :
      SignedLaplacianMethodTag

    payloadMethodIsSigned :
      payloadMethod ≡ signedContradictionResidualLaplacian

open RegistryPayload public

coordinateFromRegistryPayload :
  RegistryPayload →
  Vector.VectorCoordinate
coordinateFromRegistryPayload payload =
  Vector.vectorCoordinate
    (absoluteDegree (payloadDegree payload))
    "coordinate = F(registry_payload)"

record CoordinateRebuildabilityWitness : Set where
  constructor coordinateRebuildabilityWitness
  field
    registry :
      RegistryPayload

    coordinate :
      Vector.VectorCoordinate

    rebuildFunction :
      RegistryPayload →
      Vector.VectorCoordinate

    coordinateIsRebuilt :
      coordinate ≡ rebuildFunction registry

    rebuildable :
      Bool

    registryPayloadIsAuthority :
      Bool

open CoordinateRebuildabilityWitness public

mkCoordinateRebuildabilityWitness :
  RegistryPayload →
  CoordinateRebuildabilityWitness
mkCoordinateRebuildabilityWitness payload =
  coordinateRebuildabilityWitness
    payload
    (coordinateFromRegistryPayload payload)
    coordinateFromRegistryPayload
    refl
    true
    true

canonicalRegistryPayload :
  RegistryPayload
canonicalRegistryPayload =
  registryPayload
    Core.canonicalPredicateObjectRef
    (Graph.pnfGraphVertex zero)
    canonicalSignedAdjacencyRow
    canonicalAbsoluteDegreeOperatorRow
    signedContradictionResidualLaplacian
    refl

canonicalRebuildabilityWitness :
  CoordinateRebuildabilityWitness
canonicalRebuildabilityWitness =
  mkCoordinateRebuildabilityWitness canonicalRegistryPayload

canonicalWitnessCoordinateIsRebuilt :
  coordinate canonicalRebuildabilityWitness
  ≡
  coordinateFromRegistryPayload (registry canonicalRebuildabilityWitness)
canonicalWitnessCoordinateIsRebuilt =
  refl

canonicalWitnessIsRebuildable :
  rebuildable canonicalRebuildabilityWitness ≡ true
canonicalWitnessIsRebuildable =
  refl

------------------------------------------------------------------------
-- Spectral coordinate map rows and text fallback rendering rows.

record SpectralCoordinateMapRow : Set where
  constructor spectralCoordinateMapRow
  field
    mapObject :
      Core.PredicateObjectRef

    mapMethod :
      EmbeddingMethodDistinction

    mapCoordinate :
      Vector.VectorCoordinate

    mapWitness :
      CoordinateRebuildabilityWitness

    mapCoordinateIsWitnessCoordinate :
      mapCoordinate ≡ coordinate mapWitness

    mapRowAdmissible :
      Bool

    mapRowCarriesTextFallback :
      Bool

    mapRowCarriesVectorAuthority :
      Bool

open SpectralCoordinateMapRow public

mkSpectralCoordinateMapRow :
  CoordinateRebuildabilityWitness →
  SpectralCoordinateMapRow
mkSpectralCoordinateMapRow witness =
  spectralCoordinateMapRow
    (payloadObject (registry witness))
    canonicalSpectralMethodDistinction
    (coordinate witness)
    witness
    refl
    true
    false
    false

canonicalSpectralCoordinateMapRow :
  SpectralCoordinateMapRow
canonicalSpectralCoordinateMapRow =
  mkSpectralCoordinateMapRow canonicalRebuildabilityWitness

canonicalSpectralMapRowAdmissible :
  mapRowAdmissible canonicalSpectralCoordinateMapRow ≡ true
canonicalSpectralMapRowAdmissible =
  refl

canonicalSpectralMapRowNoTextFallback :
  mapRowCarriesTextFallback canonicalSpectralCoordinateMapRow ≡ false
canonicalSpectralMapRowNoTextFallback =
  refl

record TextualFallbackRenderingRow : Set where
  constructor textualFallbackRenderingRow
  field
    fallbackObject :
      Core.PredicateObjectRef

    fallbackRenderedText :
      String

    fallbackMethod :
      EmbeddingMethodDistinction

    fallbackCoordinate :
      Vector.VectorCoordinate

    fallbackIsRenderable :
      Bool

    fallbackIsRebuildableCoordinate :
      Bool

    fallbackAdmissibleAsSpectralRow :
      Bool

    fallbackCarriesAuthority :
      Bool

open TextualFallbackRenderingRow public

canonicalTextFallbackRenderingRow :
  TextualFallbackRenderingRow
canonicalTextFallbackRenderingRow =
  textualFallbackRenderingRow
    Core.canonicalPredicateObjectRef
    "textual fallback: render object label only; do not treat as rebuildable spectral coordinate"
    canonicalTextFallbackMethodDistinction
    (Vector.vectorCoordinate zero "text-fallback-not-rebuildable")
    true
    false
    false
    false

canonicalTextFallbackRenderable :
  fallbackIsRenderable canonicalTextFallbackRenderingRow ≡ true
canonicalTextFallbackRenderable =
  refl

canonicalTextFallbackNotAdmissible :
  fallbackAdmissibleAsSpectralRow canonicalTextFallbackRenderingRow ≡ false
canonicalTextFallbackNotAdmissible =
  refl

canonicalTextFallbackCarriesNoAuthority :
  fallbackCarriesAuthority canonicalTextFallbackRenderingRow ≡ false
canonicalTextFallbackCarriesNoAuthority =
  refl

------------------------------------------------------------------------
-- Inadmissible non-rebuildable rows.

record NonRebuildableCoordinateRow : Set where
  constructor nonRebuildableCoordinateRow
  field
    nonRebuildableObject :
      Core.PredicateObjectRef

    nonRebuildableCoordinate :
      Vector.VectorCoordinate

    nonRebuildableReason :
      String

    nonRebuildableHasRegistryPayload :
      Bool

    nonRebuildableHasCoordinateEquation :
      Bool

    nonRebuildableAdmissible :
      Bool

    nonRebuildablePromotesVectorAuthority :
      Bool

open NonRebuildableCoordinateRow public

canonicalNonRebuildableCoordinateRow :
  NonRebuildableCoordinateRow
canonicalNonRebuildableCoordinateRow =
  nonRebuildableCoordinateRow
    Core.canonicalPredicateObjectRef
    (Vector.vectorCoordinate zero "missing-registry-payload")
    "No registry payload, no coordinate = F(registry_payload) witness, and no admissible spectral row."
    false
    false
    false
    false

canonicalNonRebuildableInadmissible :
  nonRebuildableAdmissible canonicalNonRebuildableCoordinateRow ≡ false
canonicalNonRebuildableInadmissible =
  refl

canonicalNonRebuildableHasNoEquation :
  nonRebuildableHasCoordinateEquation canonicalNonRebuildableCoordinateRow
  ≡
  false
canonicalNonRebuildableHasNoEquation =
  refl

data AdmissibleCoordinateRow : Set where
  admissibleSpectralCoordinateRow :
    (row : SpectralCoordinateMapRow) →
    mapRowAdmissible row ≡ true →
    AdmissibleCoordinateRow

data NonRebuildablePromotion : Set where

nonRebuildablePromotionImpossible :
  NonRebuildablePromotion →
  ⊥
nonRebuildablePromotionImpossible ()

------------------------------------------------------------------------
-- Vector non-authority gates.

data VectorAuthorityPromotion : Set where

vectorAuthorityPromotionImpossible :
  VectorAuthorityPromotion →
  ⊥
vectorAuthorityPromotionImpossible ()

vectorCoordinateIsTruth :
  Bool
vectorCoordinateIsTruth =
  false

vectorCoordinateIsCommittedSupport :
  Bool
vectorCoordinateIsCommittedSupport =
  false

vectorCoordinateIsAdmissibility :
  Bool
vectorCoordinateIsAdmissibility =
  false

vectorCoordinateIsRegistryAuthority :
  Bool
vectorCoordinateIsRegistryAuthority =
  false

textFallbackIsCoordinateAuthority :
  Bool
textFallbackIsCoordinateAuthority =
  false

vectorCoordinateTruthFalse :
  vectorCoordinateIsTruth ≡ false
vectorCoordinateTruthFalse =
  refl

vectorCoordinateCommittedSupportFalse :
  vectorCoordinateIsCommittedSupport ≡ false
vectorCoordinateCommittedSupportFalse =
  refl

vectorCoordinateAdmissibilityFalse :
  vectorCoordinateIsAdmissibility ≡ false
vectorCoordinateAdmissibilityFalse =
  refl

vectorCoordinateRegistryAuthorityFalse :
  vectorCoordinateIsRegistryAuthority ≡ false
vectorCoordinateRegistryAuthorityFalse =
  refl

textFallbackCoordinateAuthorityFalse :
  textFallbackIsCoordinateAuthority ≡ false
textFallbackCoordinateAuthorityFalse =
  refl

canonicalVectorRowForCoordinate :
  Vector.VectorIndexRow
canonicalVectorRowForCoordinate =
  Vector.vectorIndexRow
    Vector.signedResidualLaplacianV1
    (coordinate canonicalRebuildabilityWitness)
    (Vector.objectRef Core.canonicalPredicateObjectRef "rebuildable-coordinate-object")
    true
    false
    false
    false

canonicalVectorRowProximityOnly :
  Vector.rowProximityOnly canonicalVectorRowForCoordinate ≡ true
canonicalVectorRowProximityOnly =
  refl

canonicalVectorRowNoCommittedSupport :
  Vector.rowCarriesCommittedSupport canonicalVectorRowForCoordinate ≡ false
canonicalVectorRowNoCommittedSupport =
  refl

canonicalVectorRowNoTruth :
  Vector.rowCarriesTruth canonicalVectorRowForCoordinate ≡ false
canonicalVectorRowNoTruth =
  refl

canonicalVectorRowNoAdmissibility :
  Vector.rowCarriesAdmissibility canonicalVectorRowForCoordinate ≡ false
canonicalVectorRowNoAdmissibility =
  refl

------------------------------------------------------------------------
-- End-to-end coordinate rebuildability receipt.

coordinateRebuildabilityStatement : String
coordinateRebuildabilityStatement =
  "A spectral coordinate row is rebuildable only when its coordinate is definitionally equal to F(registry_payload). Signed adjacency, absolute degree, and signed Laplacian tags are finite registry payload fields."

textFallbackBoundaryStatement : String
textFallbackBoundaryStatement =
  "Text fallback rendering is a label/display row only. It is not a rebuildability witness, not an admissible spectral coordinate row, and not vector or ITIR authority."

vectorNonAuthorityBoundaryStatement : String
vectorNonAuthorityBoundaryStatement =
  "Vector rows over rebuilt coordinates remain proximity-only rows: they carry no truth, no committed support, no admissibility, and no registry authority."

record PNFSpectralCoordinateRebuildabilityReceipt : Set where
  constructor pnfSpectralCoordinateRebuildabilityReceipt
  field
    status :
      CoordinateRebuildabilityStatus

    statusIsChecked :
      status
      ≡
      checkedCoordinateRebuildability_noTextPromotion

    components :
      List CoordinateReceiptComponent

    componentsAreCanonical :
      components ≡ canonicalCoordinateReceiptComponents

    signedAdjacency :
      SignedAdjacencyRow

    signedAdjacencyIsCanonical :
      signedAdjacency ≡ canonicalSignedAdjacencyRow

    signedAdjacencyContradictionIsNegative :
      Graph.sign (signedWeight signedAdjacency)
      ≡
      Graph.negativeResidualWeight

    absoluteDegreeRow :
      AbsoluteDegreeOperatorRow

    absoluteDegreeRowIsCanonical :
      absoluteDegreeRow ≡ canonicalAbsoluteDegreeOperatorRow

    absoluteDegreeValue :
      absoluteDegree absoluteDegreeRow ≡ 9

    laplacianMethods :
      List SignedLaplacianMethodTag

    laplacianMethodsAreCanonical :
      laplacianMethods ≡ canonicalSignedLaplacianMethods

    spectralMethod :
      EmbeddingMethodDistinction

    spectralMethodIsCanonical :
      spectralMethod ≡ canonicalSpectralMethodDistinction

    textFallbackMethod :
      EmbeddingMethodDistinction

    textFallbackMethodIsCanonical :
      textFallbackMethod ≡ canonicalTextFallbackMethodDistinction

    registryPayloadRow :
      RegistryPayload

    registryPayloadRowIsCanonical :
      registryPayloadRow ≡ canonicalRegistryPayload

    rebuildabilityWitness :
      CoordinateRebuildabilityWitness

    rebuildabilityWitnessIsCanonical :
      rebuildabilityWitness ≡ canonicalRebuildabilityWitness

    coordinateRebuildsFromPayload :
      coordinate rebuildabilityWitness
      ≡
      coordinateFromRegistryPayload (registry rebuildabilityWitness)

    spectralCoordinateRow :
      SpectralCoordinateMapRow

    spectralCoordinateRowIsCanonical :
      spectralCoordinateRow ≡ canonicalSpectralCoordinateMapRow

    spectralCoordinateRowAdmissible :
      mapRowAdmissible spectralCoordinateRow ≡ true

    textFallbackRow :
      TextualFallbackRenderingRow

    textFallbackRowIsCanonical :
      textFallbackRow ≡ canonicalTextFallbackRenderingRow

    textFallbackRowInadmissible :
      fallbackAdmissibleAsSpectralRow textFallbackRow ≡ false

    nonRebuildableRow :
      NonRebuildableCoordinateRow

    nonRebuildableRowIsCanonical :
      nonRebuildableRow ≡ canonicalNonRebuildableCoordinateRow

    nonRebuildableRowInadmissible :
      nonRebuildableAdmissible nonRebuildableRow ≡ false

    vectorRow :
      Vector.VectorIndexRow

    vectorRowIsCanonical :
      vectorRow ≡ canonicalVectorRowForCoordinate

    vectorRowProximityOnlyHere :
      Vector.rowProximityOnly vectorRow ≡ true

    vectorRowCommittedSupportFalse :
      Vector.rowCarriesCommittedSupport vectorRow ≡ false

    vectorRowTruthFalse :
      Vector.rowCarriesTruth vectorRow ≡ false

    vectorRowAdmissibilityFalse :
      Vector.rowCarriesAdmissibility vectorRow ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ coordinateRebuildabilityStatement

    textFallbackBoundary :
      String

    textFallbackBoundaryIsCanonical :
      textFallbackBoundary ≡ textFallbackBoundaryStatement

    vectorBoundary :
      String

    vectorBoundaryIsCanonical :
      vectorBoundary ≡ vectorNonAuthorityBoundaryStatement

    vectorTruthGate :
      Bool

    vectorTruthGateIsFalse :
      vectorTruthGate ≡ false

    vectorSupportGate :
      Bool

    vectorSupportGateIsFalse :
      vectorSupportGate ≡ false

    vectorAdmissibilityGate :
      Bool

    vectorAdmissibilityGateIsFalse :
      vectorAdmissibilityGate ≡ false

    textFallbackAuthorityGate :
      Bool

    textFallbackAuthorityGateIsFalse :
      textFallbackAuthorityGate ≡ false

    vectorAuthorityPromotions :
      List VectorAuthorityPromotion

    vectorAuthorityPromotionsAreEmpty :
      vectorAuthorityPromotions ≡ []

    nonRebuildablePromotions :
      List NonRebuildablePromotion

    nonRebuildablePromotionsAreEmpty :
      nonRebuildablePromotions ≡ []

open PNFSpectralCoordinateRebuildabilityReceipt public

canonicalPNFSpectralCoordinateRebuildabilityReceipt :
  PNFSpectralCoordinateRebuildabilityReceipt
canonicalPNFSpectralCoordinateRebuildabilityReceipt =
  pnfSpectralCoordinateRebuildabilityReceipt
    checkedCoordinateRebuildability_noTextPromotion
    refl
    canonicalCoordinateReceiptComponents
    refl
    canonicalSignedAdjacencyRow
    refl
    refl
    canonicalAbsoluteDegreeOperatorRow
    refl
    refl
    canonicalSignedLaplacianMethods
    refl
    canonicalSpectralMethodDistinction
    refl
    canonicalTextFallbackMethodDistinction
    refl
    canonicalRegistryPayload
    refl
    canonicalRebuildabilityWitness
    refl
    refl
    canonicalSpectralCoordinateMapRow
    refl
    refl
    canonicalTextFallbackRenderingRow
    refl
    refl
    canonicalNonRebuildableCoordinateRow
    refl
    refl
    canonicalVectorRowForCoordinate
    refl
    refl
    refl
    refl
    refl
    coordinateRebuildabilityStatement
    refl
    textFallbackBoundaryStatement
    refl
    vectorNonAuthorityBoundaryStatement
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    []
    refl
    []
    refl

canonicalReceiptCoordinateRebuilds :
  coordinate (rebuildabilityWitness canonicalPNFSpectralCoordinateRebuildabilityReceipt)
  ≡
  coordinateFromRegistryPayload
    (registry (rebuildabilityWitness canonicalPNFSpectralCoordinateRebuildabilityReceipt))
canonicalReceiptCoordinateRebuilds =
  refl

canonicalReceiptTextFallbackInadmissible :
  fallbackAdmissibleAsSpectralRow
    (textFallbackRow canonicalPNFSpectralCoordinateRebuildabilityReceipt)
  ≡
  false
canonicalReceiptTextFallbackInadmissible =
  refl

canonicalReceiptVectorNonAuthority :
  Vector.rowCarriesTruth
    (vectorRow canonicalPNFSpectralCoordinateRebuildabilityReceipt)
  ≡
  false
canonicalReceiptVectorNonAuthority =
  refl

canonicalReceiptNonRebuildableInadmissible :
  nonRebuildableAdmissible
    (nonRebuildableRow canonicalPNFSpectralCoordinateRebuildabilityReceipt)
  ≡
  false
canonicalReceiptNonRebuildableInadmissible =
  refl

canonicalReceipt :
  PNFSpectralCoordinateRebuildabilityReceipt
canonicalReceipt =
  canonicalPNFSpectralCoordinateRebuildabilityReceipt
