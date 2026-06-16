module DASHI.Interop.PNFHodgeResidualTopology where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFBraidTransportField as Braid
import DASHI.Interop.PNFSpectralFieldCore as Core
import DASHI.Interop.PNFSpectralFieldGraph as Graph
import DASHI.Interop.SpectralOperatorShapeCore as ShapeCore
import DASHI.Interop.SensibLawResidualLattice as Residual
import UFTC_Lattice as UFTC

------------------------------------------------------------------------
-- PNF residual topology and Hodge receipt boundary.
--
-- This module is a checked symbolic topology surface only.  It names finite
-- 0/1/2-cell references, residual and transport edges, triangle-shaped
-- residual witnesses, boundary-shape tags, Hodge Laplacian tags, and detected
-- feature tags.  Signed residual graph Laplacians are explicitly marked as the
-- implementable first layer; Hodge authority remains fail-closed.

data PNFHodgeResidualTopologyStatus : Set where
  residualTopologyReceipt_noHodgeAuthorityPromotion :
    PNFHodgeResidualTopologyStatus

data PNFCellDimension : Set where
  zeroCellDimension : PNFCellDimension
  oneCellDimension : PNFCellDimension
  twoCellDimension : PNFCellDimension

data PNFZeroCellRef : Set where
  pnfZeroCellRef : Nat → PNFZeroCellRef
  pnfZeroCellFallback : PNFZeroCellRef

data PNFOneCellRef : Set where
  pnfOneCellRef : Nat → PNFOneCellRef
  pnfResidualOneCell :
    Core.ResidualEdgeRef →
    PNFOneCellRef
  pnfTransportOneCell :
    Core.BraidPathRef →
    PNFOneCellRef
  pnfGraphOneCell :
    Graph.PNFGraphEdge →
    PNFOneCellRef
  pnfOneCellFallback : PNFOneCellRef

data PNFTwoCellRef : Set where
  pnfTwoCellRef : Nat → PNFTwoCellRef
  pnfTwoCellFallback : PNFTwoCellRef

record PNFZeroCell : Set where
  constructor pnfZeroCell
  field
    zeroCellRef :
      PNFZeroCellRef

    predicateObject :
      Core.PredicateObjectRef

    graphVertex :
      Graph.PNFGraphVertex

    zeroCellLabel :
      String

open PNFZeroCell public

data PNFOneCellKind : Set where
  residualEdge1Cell :
    PNFOneCellKind

  transportEdge1Cell :
    PNFOneCellKind

  braidWitness1Cell :
    PNFOneCellKind

  contradictionResidual1Cell :
    PNFOneCellKind

record PNFOneCell : Set where
  constructor pnfOneCell
  field
    oneCellRef :
      PNFOneCellRef

    oneCellKind :
      PNFOneCellKind

    oneCellSource :
      PNFZeroCellRef

    oneCellTarget :
      PNFZeroCellRef

    residualLevel :
      Residual.ResidualLevel

    graphWeight :
      Graph.SignedResidualWeight

    transportOnly :
      Bool

    oneCellIsReceiptOnly :
      Bool

    oneCellIsReceiptOnlyIsTrue :
      oneCellIsReceiptOnly ≡ true

open PNFOneCell public

data PNFTwoCellKind : Set where
  meetTriangle2Cell :
    PNFTwoCellKind

  joinTriangle2Cell :
    PNFTwoCellKind

  contradictionTriangle2Cell :
    PNFTwoCellKind

record PNFTriangleBoundary : Set where
  constructor pnfTriangleBoundary
  field
    edge01 :
      PNFOneCellRef

    edge12 :
      PNFOneCellRef

    edge20 :
      PNFOneCellRef

open PNFTriangleBoundary public

record PNFTwoCell : Set where
  constructor pnfTwoCell
  field
    twoCellRef :
      PNFTwoCellRef

    twoCellKind :
      PNFTwoCellKind

    triangleBoundary :
      PNFTriangleBoundary

    triangleResidual :
      Residual.ResidualLevel

    twoCellIsReceiptOnly :
      Bool

    twoCellIsReceiptOnlyIsTrue :
      twoCellIsReceiptOnly ≡ true

open PNFTwoCell public

------------------------------------------------------------------------
-- Boundary map shapes and finite signed Laplacian tags.

data BoundaryMapShapeTag : Set where
  d0 : BoundaryMapShapeTag
  d1 : BoundaryMapShapeTag

record BoundaryMapShape : Set where
  constructor boundaryMapShape
  field
    boundaryTag :
      BoundaryMapShapeTag

    boundaryDomain :
      PNFCellDimension

    boundaryCodomain :
      PNFCellDimension

    signedIncidenceShape :
      Bool

    signedIncidenceShapeIsTrue :
      signedIncidenceShape ≡ true

open BoundaryMapShape public

d0BoundaryShape : BoundaryMapShape
d0BoundaryShape =
  boundaryMapShape
    d0
    oneCellDimension
    zeroCellDimension
    true
    refl

d1BoundaryShape : BoundaryMapShape
d1BoundaryShape =
  boundaryMapShape
    d1
    twoCellDimension
    oneCellDimension
    true
    refl

data HodgeLaplacianTag : Set where
  Δ0 : HodgeLaplacianTag
  Δ1 : HodgeLaplacianTag
  Δ2 : HodgeLaplacianTag

data HodgeLaplacianBoundaryLayer : Set where
  signedGraphLaplacian0Implementable :
    HodgeLaplacianBoundaryLayer

  hodgeLaplacian1DiagnosticOnly :
    HodgeLaplacianBoundaryLayer

  hodgeLaplacian2DiagnosticOnly :
    HodgeLaplacianBoundaryLayer

laplacianBoundaryLayer :
  HodgeLaplacianTag →
  HodgeLaplacianBoundaryLayer
laplacianBoundaryLayer Δ0 =
  signedGraphLaplacian0Implementable
laplacianBoundaryLayer Δ1 =
  hodgeLaplacian1DiagnosticOnly
laplacianBoundaryLayer Δ2 =
  hodgeLaplacian2DiagnosticOnly

laplacianIsSignedGraphLaplacian0 :
  HodgeLaplacianTag →
  Bool
laplacianIsSignedGraphLaplacian0 Δ0 =
  true
laplacianIsSignedGraphLaplacian0 Δ1 =
  false
laplacianIsSignedGraphLaplacian0 Δ2 =
  false

laplacianIsRicherHodgeDiagnosticOnly :
  HodgeLaplacianTag →
  Bool
laplacianIsRicherHodgeDiagnosticOnly Δ0 =
  false
laplacianIsRicherHodgeDiagnosticOnly Δ1 =
  true
laplacianIsRicherHodgeDiagnosticOnly Δ2 =
  true

laplacianCellDimension :
  HodgeLaplacianTag →
  PNFCellDimension
laplacianCellDimension Δ0 =
  zeroCellDimension
laplacianCellDimension Δ1 =
  oneCellDimension
laplacianCellDimension Δ2 =
  twoCellDimension

record SignedBoundaryEntry : Set where
  constructor signedBoundaryEntry
  field
    boundaryShape :
      BoundaryMapShape

    sourceCell :
      PNFCellDimension

    targetCell :
      PNFCellDimension

    incidenceSign :
      Graph.WeightSign

    incidenceMagnitude :
      UFTC.Severity

open SignedBoundaryEntry public

record PNFHodgeLaplacianShape : Set where
  constructor pnfHodgeLaplacianShape
  field
    laplacianTag :
      HodgeLaplacianTag

    laplacianActsOn :
      PNFCellDimension

    laplacianActsOnIsCanonical :
      laplacianActsOn ≡ laplacianCellDimension laplacianTag

    laplacianLayer :
      HodgeLaplacianBoundaryLayer

    laplacianLayerIsCanonical :
      laplacianLayer ≡ laplacianBoundaryLayer laplacianTag

    lowerBoundaryShape :
      BoundaryMapShape

    upperBoundaryShape :
      BoundaryMapShape

    signedResidualImplementableFirst :
      Bool

    signedResidualImplementableFirstIsTrue :
      signedResidualImplementableFirst ≡ true

    signedGraphLaplacian0ImplementableLayer :
      Bool

    signedGraphLaplacian0ImplementableLayerIsCanonical :
      signedGraphLaplacian0ImplementableLayer
      ≡
      laplacianIsSignedGraphLaplacian0 laplacianTag

    richerHodgeDiagnosticOnlyLayer :
      Bool

    richerHodgeDiagnosticOnlyLayerIsCanonical :
      richerHodgeDiagnosticOnlyLayer
      ≡
      laplacianIsRicherHodgeDiagnosticOnly laplacianTag

    richerHodgeDiagnosticOnlyNoAuthority :
      Bool

    richerHodgeDiagnosticOnlyNoAuthorityIsFalse :
      richerHodgeDiagnosticOnlyNoAuthority ≡ false

    hodgeAuthorityGranted :
      Bool

    hodgeAuthorityGrantedIsFalse :
      hodgeAuthorityGranted ≡ false

open PNFHodgeLaplacianShape public

canonicalΔ0Shape : PNFHodgeLaplacianShape
canonicalΔ0Shape =
  pnfHodgeLaplacianShape
    Δ0
    zeroCellDimension
    refl
    signedGraphLaplacian0Implementable
    refl
    d0BoundaryShape
    d0BoundaryShape
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

canonicalΔ1Shape : PNFHodgeLaplacianShape
canonicalΔ1Shape =
  pnfHodgeLaplacianShape
    Δ1
    oneCellDimension
    refl
    hodgeLaplacian1DiagnosticOnly
    refl
    d0BoundaryShape
    d1BoundaryShape
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    false
    refl

canonicalΔ2Shape : PNFHodgeLaplacianShape
canonicalΔ2Shape =
  pnfHodgeLaplacianShape
    Δ2
    twoCellDimension
    refl
    hodgeLaplacian2DiagnosticOnly
    refl
    d1BoundaryShape
    d1BoundaryShape
    true
    refl
    false
    refl
    true
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Detected residual-field features.

data DetectedResidualFeatureTag : Set where
  cycleFeature :
    DetectedResidualFeatureTag

  holeFeature :
    DetectedResidualFeatureTag

  inconsistentLoopFeature :
    DetectedResidualFeatureTag

  unresolvedEvidenceCavityFeature :
    DetectedResidualFeatureTag

  closedContradictionStructureFeature :
    DetectedResidualFeatureTag

  frustratedSignedCycleFeature :
    DetectedResidualFeatureTag

  rotationalFrustrationFeature :
    DetectedResidualFeatureTag

  harmonicCycleDiagnosticFeature :
    DetectedResidualFeatureTag

  harmonicCavityDiagnosticFeature :
    DetectedResidualFeatureTag

canonicalDetectedResidualFeatures :
  List DetectedResidualFeatureTag
canonicalDetectedResidualFeatures =
  cycleFeature
  ∷ holeFeature
  ∷ inconsistentLoopFeature
  ∷ unresolvedEvidenceCavityFeature
  ∷ closedContradictionStructureFeature
  ∷ frustratedSignedCycleFeature
  ∷ rotationalFrustrationFeature
  ∷ harmonicCycleDiagnosticFeature
  ∷ harmonicCavityDiagnosticFeature
  ∷ []

record DetectedResidualFeature : Set where
  constructor detectedResidualFeature
  field
    featureTag :
      DetectedResidualFeatureTag

    featureWitness0Cells :
      List PNFZeroCellRef

    featureWitness1Cells :
      List PNFOneCellRef

    featureWitness2Cells :
      List PNFTwoCellRef

    featureIsDiagnosticOnly :
      Bool

    featureIsDiagnosticOnlyIsTrue :
      featureIsDiagnosticOnly ≡ true

    featureGrantsHodgeAuthority :
      Bool

    featureGrantsHodgeAuthorityIsFalse :
      featureGrantsHodgeAuthority ≡ false

open DetectedResidualFeature public

------------------------------------------------------------------------
-- Canonical finite example.

canonicalZeroCell0 : PNFZeroCell
canonicalZeroCell0 =
  pnfZeroCell
    (pnfZeroCellRef zero)
    Core.canonicalPredicateObjectRef
    (Graph.pnfGraphVertex zero)
    "canonical residual topology 0-cell A"

canonicalZeroCell1 : PNFZeroCell
canonicalZeroCell1 =
  pnfZeroCell
    (pnfZeroCellRef (suc zero))
    Core.canonicalPredicateObjectRef
    (Graph.pnfGraphVertex (suc zero))
    "canonical residual topology 0-cell B"

canonicalZeroCell2 : PNFZeroCell
canonicalZeroCell2 =
  pnfZeroCell
    (pnfZeroCellRef (suc (suc zero)))
    Core.canonicalPredicateObjectRef
    (Graph.pnfGraphVertex (suc (suc zero)))
    "canonical residual topology 0-cell C"

canonicalResidualOneCell : PNFOneCell
canonicalResidualOneCell =
  pnfOneCell
    (pnfResidualOneCell Core.residualEdgeFallback)
    residualEdge1Cell
    (zeroCellRef canonicalZeroCell0)
    (zeroCellRef canonicalZeroCell1)
    Residual.partial
    (Graph.residualSignedWeight Residual.partial)
    false
    true
    refl

canonicalTransportOneCell : PNFOneCell
canonicalTransportOneCell =
  pnfOneCell
    (pnfTransportOneCell Core.braidPathFallback)
    transportEdge1Cell
    (zeroCellRef canonicalZeroCell1)
    (zeroCellRef canonicalZeroCell2)
    Residual.noTypedMeet
    (Graph.residualSignedWeight Residual.noTypedMeet)
    true
    true
    refl

canonicalContradictionOneCell : PNFOneCell
canonicalContradictionOneCell =
  pnfOneCell
    (pnfOneCellRef (suc (suc zero)))
    contradictionResidual1Cell
    (zeroCellRef canonicalZeroCell2)
    (zeroCellRef canonicalZeroCell0)
    Residual.contradiction
    (Graph.residualSignedWeight Residual.contradiction)
    false
    true
    refl

canonicalContradictionTriangleBoundary :
  PNFTriangleBoundary
canonicalContradictionTriangleBoundary =
  pnfTriangleBoundary
    (oneCellRef canonicalResidualOneCell)
    (oneCellRef canonicalTransportOneCell)
    (oneCellRef canonicalContradictionOneCell)

canonicalContradictionTwoCell : PNFTwoCell
canonicalContradictionTwoCell =
  pnfTwoCell
    (pnfTwoCellRef zero)
    contradictionTriangle2Cell
    canonicalContradictionTriangleBoundary
    Residual.contradiction
    true
    refl

canonicalCycleFeature : DetectedResidualFeature
canonicalCycleFeature =
  detectedResidualFeature
    closedContradictionStructureFeature
    (zeroCellRef canonicalZeroCell0
      ∷ zeroCellRef canonicalZeroCell1
      ∷ zeroCellRef canonicalZeroCell2
      ∷ [])
    (oneCellRef canonicalResidualOneCell
      ∷ oneCellRef canonicalTransportOneCell
      ∷ oneCellRef canonicalContradictionOneCell
      ∷ [])
    (twoCellRef canonicalContradictionTwoCell ∷ [])
    true
    refl
    false
    refl

canonicalFrustratedSignedCycleFeature : DetectedResidualFeature
canonicalFrustratedSignedCycleFeature =
  detectedResidualFeature
    frustratedSignedCycleFeature
    (zeroCellRef canonicalZeroCell0
      ∷ zeroCellRef canonicalZeroCell1
      ∷ zeroCellRef canonicalZeroCell2
      ∷ [])
    (oneCellRef canonicalResidualOneCell
      ∷ oneCellRef canonicalContradictionOneCell
      ∷ [])
    (twoCellRef canonicalContradictionTwoCell ∷ [])
    true
    refl
    false
    refl

canonicalRotationalFrustrationFeature : DetectedResidualFeature
canonicalRotationalFrustrationFeature =
  detectedResidualFeature
    rotationalFrustrationFeature
    (zeroCellRef canonicalZeroCell0
      ∷ zeroCellRef canonicalZeroCell1
      ∷ zeroCellRef canonicalZeroCell2
      ∷ [])
    (oneCellRef canonicalResidualOneCell
      ∷ oneCellRef canonicalTransportOneCell
      ∷ oneCellRef canonicalContradictionOneCell
      ∷ [])
    (twoCellRef canonicalContradictionTwoCell ∷ [])
    true
    refl
    false
    refl

canonicalHarmonicCycleDiagnosticFeature : DetectedResidualFeature
canonicalHarmonicCycleDiagnosticFeature =
  detectedResidualFeature
    harmonicCycleDiagnosticFeature
    (zeroCellRef canonicalZeroCell0
      ∷ zeroCellRef canonicalZeroCell1
      ∷ zeroCellRef canonicalZeroCell2
      ∷ [])
    (oneCellRef canonicalResidualOneCell
      ∷ oneCellRef canonicalTransportOneCell
      ∷ oneCellRef canonicalContradictionOneCell
      ∷ [])
    (twoCellRef canonicalContradictionTwoCell ∷ [])
    true
    refl
    false
    refl

------------------------------------------------------------------------
-- Authority boundary and canonical receipt.

data PNFHodgeResidualTopologyPromotion : Set where

pnfHodgeResidualTopologyPromotionImpossible :
  PNFHodgeResidualTopologyPromotion →
  ⊥
pnfHodgeResidualTopologyPromotionImpossible ()

data PNFHodgeResidualTopologyComponent : Set where
  zeroOneTwoCellReferenceComponent :
    PNFHodgeResidualTopologyComponent

  residualAndTransportOneCellComponent :
    PNFHodgeResidualTopologyComponent

  meetJoinContradictionTriangleComponent :
    PNFHodgeResidualTopologyComponent

  d0d1BoundaryShapeComponent :
    PNFHodgeResidualTopologyComponent

  hodgeLaplacianTagComponent :
    PNFHodgeResidualTopologyComponent

  detectedFeatureTagComponent :
    PNFHodgeResidualTopologyComponent

  signedLaplacianFirstComponent :
    PNFHodgeResidualTopologyComponent

  hodgeDiagnosticOnlyComponent :
    PNFHodgeResidualTopologyComponent

  frustrationFeatureComponent :
    PNFHodgeResidualTopologyComponent

  harmonicCycleDiagnosticComponent :
    PNFHodgeResidualTopologyComponent

  failClosedHodgeAuthorityComponent :
    PNFHodgeResidualTopologyComponent

canonicalPNFHodgeResidualTopologyComponents :
  List PNFHodgeResidualTopologyComponent
canonicalPNFHodgeResidualTopologyComponents =
  zeroOneTwoCellReferenceComponent
  ∷ residualAndTransportOneCellComponent
  ∷ meetJoinContradictionTriangleComponent
  ∷ d0d1BoundaryShapeComponent
  ∷ hodgeLaplacianTagComponent
  ∷ detectedFeatureTagComponent
  ∷ signedLaplacianFirstComponent
  ∷ hodgeDiagnosticOnlyComponent
  ∷ frustrationFeatureComponent
  ∷ harmonicCycleDiagnosticComponent
  ∷ failClosedHodgeAuthorityComponent
  ∷ []

pnfHodgeResidualTopologyStatement : String
pnfHodgeResidualTopologyStatement =
  "PNFHodgeResidualTopology records a finite residual-field topology: PNF refs are 0-cells, residual and braid transport receipts are 1-cells, meet/join/contradiction triangles are 2-cells, and d0/d1 boundary shapes address signed incidence matrices."

pnfHodgeResidualTopologyBoundaryStatement : String
pnfHodgeResidualTopologyBoundaryStatement =
  "The signed residual graph Laplacian Δ0 is the implementable first layer. Richer Hodge Δ1/Δ2 tags, frustrated signed cycles, rotational frustration, and harmonic-cycle/cavity tags are diagnostic receipt shapes only; they grant no semantic truth, runtime evidence, legal/policy authority, continuum Hodge theorem, harmonic authority, or closed-loop resolution authority."

record PNFHodgeResidualTopologyReceipt : Set where
  field
    status :
      PNFHodgeResidualTopologyStatus

    statusIsReceiptNoHodgeAuthorityPromotion :
      status
      ≡
      residualTopologyReceipt_noHodgeAuthorityPromotion

    spectralCoreReceipt :
      Core.PNFSpectralFieldReceipt

    spectralCoreReceiptIsCanonical :
      spectralCoreReceipt ≡ Core.canonicalPNFSpectralFieldReceipt

    spectralGraphReceipt :
      Graph.PNFSpectralFieldGraphReceipt

    spectralGraphReceiptIsCanonical :
      spectralGraphReceipt ≡ Graph.canonicalPNFSpectralFieldGraphReceipt

    braidTransportStatus :
      Braid.PNFBraidTransportStatus

    braidTransportStatusIsNoPromotion :
      braidTransportStatus
      ≡
      Braid.pnfBraidTransportRecordedNoPromotion

    components :
      List PNFHodgeResidualTopologyComponent

    componentsAreCanonical :
      components ≡ canonicalPNFHodgeResidualTopologyComponents

    d0Shape :
      BoundaryMapShape

    d0ShapeIsCanonical :
      d0Shape ≡ d0BoundaryShape

    d1Shape :
      BoundaryMapShape

    d1ShapeIsCanonical :
      d1Shape ≡ d1BoundaryShape

    Δ0Shape :
      PNFHodgeLaplacianShape

    Δ0ShapeIsCanonical :
      Δ0Shape ≡ canonicalΔ0Shape

    Δ1Shape :
      PNFHodgeLaplacianShape

    Δ1ShapeIsCanonical :
      Δ1Shape ≡ canonicalΔ1Shape

    Δ2Shape :
      PNFHodgeLaplacianShape

    Δ2ShapeIsCanonical :
      Δ2Shape ≡ canonicalΔ2Shape

    hodge1OperatorShapeCore :
      ShapeCore.SpectralOperatorShapeReceipt

    hodge1OperatorShapeCoreIsCanonical :
      hodge1OperatorShapeCore
      ≡
      ShapeCore.canonicalHodge1DiagnosticReceipt

    hodge2OperatorShapeCore :
      ShapeCore.SpectralOperatorShapeReceipt

    hodge2OperatorShapeCoreIsCanonical :
      hodge2OperatorShapeCore
      ≡
      ShapeCore.canonicalHodge2DiagnosticReceipt

    hodgeOperatorShapeCoreAuthorityFalse :
      ShapeCore.higherHodgeDiagnosticGrantsAuthority
        hodge1OperatorShapeCore
      ≡
      false

    detectedFeatureTags :
      List DetectedResidualFeatureTag

    detectedFeatureTagsAreCanonical :
      detectedFeatureTags ≡ canonicalDetectedResidualFeatures

    exampleZeroCell :
      PNFZeroCell

    exampleZeroCellIsCanonical :
      exampleZeroCell ≡ canonicalZeroCell0

    exampleResidualOneCell :
      PNFOneCell

    exampleResidualOneCellIsCanonical :
      exampleResidualOneCell ≡ canonicalResidualOneCell

    exampleTransportOneCell :
      PNFOneCell

    exampleTransportOneCellIsCanonical :
      exampleTransportOneCell ≡ canonicalTransportOneCell

    exampleContradictionTwoCell :
      PNFTwoCell

    exampleContradictionTwoCellIsCanonical :
      exampleContradictionTwoCell ≡ canonicalContradictionTwoCell

    exampleDetectedFeature :
      DetectedResidualFeature

    exampleDetectedFeatureIsCanonical :
      exampleDetectedFeature ≡ canonicalCycleFeature

    signedResidualLaplacianImplementableFirst :
      Bool

    signedResidualLaplacianImplementableFirstIsTrue :
      signedResidualLaplacianImplementableFirst ≡ true

    Δ0SignedGraphLaplacianImplementable :
      Bool

    Δ0SignedGraphLaplacianImplementableIsTrue :
      Δ0SignedGraphLaplacianImplementable ≡ true

    Δ1HodgeLaplacianDiagnosticOnly :
      Bool

    Δ1HodgeLaplacianDiagnosticOnlyIsTrue :
      Δ1HodgeLaplacianDiagnosticOnly ≡ true

    Δ2HodgeLaplacianDiagnosticOnly :
      Bool

    Δ2HodgeLaplacianDiagnosticOnlyIsTrue :
      Δ2HodgeLaplacianDiagnosticOnly ≡ true

    exampleFrustratedSignedCycleFeature :
      DetectedResidualFeature

    exampleFrustratedSignedCycleFeatureIsCanonical :
      exampleFrustratedSignedCycleFeature
      ≡
      canonicalFrustratedSignedCycleFeature

    exampleRotationalFrustrationFeature :
      DetectedResidualFeature

    exampleRotationalFrustrationFeatureIsCanonical :
      exampleRotationalFrustrationFeature
      ≡
      canonicalRotationalFrustrationFeature

    exampleHarmonicCycleDiagnosticFeature :
      DetectedResidualFeature

    exampleHarmonicCycleDiagnosticFeatureIsCanonical :
      exampleHarmonicCycleDiagnosticFeature
      ≡
      canonicalHarmonicCycleDiagnosticFeature

    hodgeAuthorityPromotion :
      Bool

    hodgeAuthorityPromotionIsFalse :
      hodgeAuthorityPromotion ≡ false

    hodgeDecompositionAuthorityPromotion :
      Bool

    hodgeDecompositionAuthorityPromotionIsFalse :
      hodgeDecompositionAuthorityPromotion ≡ false

    harmonicCycleAuthorityPromotion :
      Bool

    harmonicCycleAuthorityPromotionIsFalse :
      harmonicCycleAuthorityPromotion ≡ false

    topologyDecisionAuthorityPromotion :
      Bool

    topologyDecisionAuthorityPromotionIsFalse :
      topologyDecisionAuthorityPromotion ≡ false

    runtimeEvidencePromotion :
      Bool

    runtimeEvidencePromotionIsFalse :
      runtimeEvidencePromotion ≡ false

    closedLoopResolutionPromotion :
      Bool

    closedLoopResolutionPromotionIsFalse :
      closedLoopResolutionPromotion ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ pnfHodgeResidualTopologyStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ pnfHodgeResidualTopologyBoundaryStatement

    promotionFlags :
      List PNFHodgeResidualTopologyPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open PNFHodgeResidualTopologyReceipt public

canonicalPNFHodgeResidualTopologyReceipt :
  PNFHodgeResidualTopologyReceipt
canonicalPNFHodgeResidualTopologyReceipt =
  record
    { status =
        residualTopologyReceipt_noHodgeAuthorityPromotion
    ; statusIsReceiptNoHodgeAuthorityPromotion =
        refl
    ; spectralCoreReceipt =
        Core.canonicalPNFSpectralFieldReceipt
    ; spectralCoreReceiptIsCanonical =
        refl
    ; spectralGraphReceipt =
        Graph.canonicalPNFSpectralFieldGraphReceipt
    ; spectralGraphReceiptIsCanonical =
        refl
    ; braidTransportStatus =
        Braid.pnfBraidTransportRecordedNoPromotion
    ; braidTransportStatusIsNoPromotion =
        refl
    ; components =
        canonicalPNFHodgeResidualTopologyComponents
    ; componentsAreCanonical =
        refl
    ; d0Shape =
        d0BoundaryShape
    ; d0ShapeIsCanonical =
        refl
    ; d1Shape =
        d1BoundaryShape
    ; d1ShapeIsCanonical =
        refl
    ; Δ0Shape =
        canonicalΔ0Shape
    ; Δ0ShapeIsCanonical =
        refl
    ; Δ1Shape =
        canonicalΔ1Shape
    ; Δ1ShapeIsCanonical =
        refl
    ; Δ2Shape =
        canonicalΔ2Shape
    ; Δ2ShapeIsCanonical =
        refl
    ; hodge1OperatorShapeCore =
        ShapeCore.canonicalHodge1DiagnosticReceipt
    ; hodge1OperatorShapeCoreIsCanonical =
        refl
    ; hodge2OperatorShapeCore =
        ShapeCore.canonicalHodge2DiagnosticReceipt
    ; hodge2OperatorShapeCoreIsCanonical =
        refl
    ; hodgeOperatorShapeCoreAuthorityFalse =
        refl
    ; detectedFeatureTags =
        canonicalDetectedResidualFeatures
    ; detectedFeatureTagsAreCanonical =
        refl
    ; exampleZeroCell =
        canonicalZeroCell0
    ; exampleZeroCellIsCanonical =
        refl
    ; exampleResidualOneCell =
        canonicalResidualOneCell
    ; exampleResidualOneCellIsCanonical =
        refl
    ; exampleTransportOneCell =
        canonicalTransportOneCell
    ; exampleTransportOneCellIsCanonical =
        refl
    ; exampleContradictionTwoCell =
        canonicalContradictionTwoCell
    ; exampleContradictionTwoCellIsCanonical =
        refl
    ; exampleDetectedFeature =
        canonicalCycleFeature
    ; exampleDetectedFeatureIsCanonical =
        refl
    ; signedResidualLaplacianImplementableFirst =
        true
    ; signedResidualLaplacianImplementableFirstIsTrue =
        refl
    ; Δ0SignedGraphLaplacianImplementable =
        true
    ; Δ0SignedGraphLaplacianImplementableIsTrue =
        refl
    ; Δ1HodgeLaplacianDiagnosticOnly =
        true
    ; Δ1HodgeLaplacianDiagnosticOnlyIsTrue =
        refl
    ; Δ2HodgeLaplacianDiagnosticOnly =
        true
    ; Δ2HodgeLaplacianDiagnosticOnlyIsTrue =
        refl
    ; exampleFrustratedSignedCycleFeature =
        canonicalFrustratedSignedCycleFeature
    ; exampleFrustratedSignedCycleFeatureIsCanonical =
        refl
    ; exampleRotationalFrustrationFeature =
        canonicalRotationalFrustrationFeature
    ; exampleRotationalFrustrationFeatureIsCanonical =
        refl
    ; exampleHarmonicCycleDiagnosticFeature =
        canonicalHarmonicCycleDiagnosticFeature
    ; exampleHarmonicCycleDiagnosticFeatureIsCanonical =
        refl
    ; hodgeAuthorityPromotion =
        false
    ; hodgeAuthorityPromotionIsFalse =
        refl
    ; hodgeDecompositionAuthorityPromotion =
        false
    ; hodgeDecompositionAuthorityPromotionIsFalse =
        refl
    ; harmonicCycleAuthorityPromotion =
        false
    ; harmonicCycleAuthorityPromotionIsFalse =
        refl
    ; topologyDecisionAuthorityPromotion =
        false
    ; topologyDecisionAuthorityPromotionIsFalse =
        refl
    ; runtimeEvidencePromotion =
        false
    ; runtimeEvidencePromotionIsFalse =
        refl
    ; closedLoopResolutionPromotion =
        false
    ; closedLoopResolutionPromotionIsFalse =
        refl
    ; statement =
        pnfHodgeResidualTopologyStatement
    ; statementIsCanonical =
        refl
    ; boundary =
        pnfHodgeResidualTopologyBoundaryStatement
    ; boundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

canonicalReceiptD0TagIsD0 :
  boundaryTag
    (d0Shape canonicalPNFHodgeResidualTopologyReceipt)
  ≡
  d0
canonicalReceiptD0TagIsD0 =
  refl

canonicalReceiptD1TagIsD1 :
  boundaryTag
    (d1Shape canonicalPNFHodgeResidualTopologyReceipt)
  ≡
  d1
canonicalReceiptD1TagIsD1 =
  refl

canonicalReceiptΔ0ActsOnZeroCells :
  laplacianActsOn
    (Δ0Shape canonicalPNFHodgeResidualTopologyReceipt)
  ≡
  zeroCellDimension
canonicalReceiptΔ0ActsOnZeroCells =
  refl

canonicalReceiptΔ1ActsOnOneCells :
  laplacianActsOn
    (Δ1Shape canonicalPNFHodgeResidualTopologyReceipt)
  ≡
  oneCellDimension
canonicalReceiptΔ1ActsOnOneCells =
  refl

canonicalReceiptΔ2ActsOnTwoCells :
  laplacianActsOn
    (Δ2Shape canonicalPNFHodgeResidualTopologyReceipt)
  ≡
  twoCellDimension
canonicalReceiptΔ2ActsOnTwoCells =
  refl

canonicalReceiptSignedLaplacianFirst :
  signedResidualLaplacianImplementableFirst
    canonicalPNFHodgeResidualTopologyReceipt
  ≡
  true
canonicalReceiptSignedLaplacianFirst =
  refl

canonicalReceiptΔ0IsSignedGraphImplementable :
  laplacianLayer
    (Δ0Shape canonicalPNFHodgeResidualTopologyReceipt)
  ≡
  signedGraphLaplacian0Implementable
canonicalReceiptΔ0IsSignedGraphImplementable =
  refl

canonicalReceiptΔ1IsDiagnosticOnly :
  laplacianLayer
    (Δ1Shape canonicalPNFHodgeResidualTopologyReceipt)
  ≡
  hodgeLaplacian1DiagnosticOnly
canonicalReceiptΔ1IsDiagnosticOnly =
  refl

canonicalReceiptΔ2IsDiagnosticOnly :
  laplacianLayer
    (Δ2Shape canonicalPNFHodgeResidualTopologyReceipt)
  ≡
  hodgeLaplacian2DiagnosticOnly
canonicalReceiptΔ2IsDiagnosticOnly =
  refl

canonicalReceiptHodgeAuthorityFailClosed :
  hodgeAuthorityPromotion
    canonicalPNFHodgeResidualTopologyReceipt
  ≡
  false
canonicalReceiptHodgeAuthorityFailClosed =
  refl

canonicalReceiptHodgeDecompositionAuthorityFailClosed :
  hodgeDecompositionAuthorityPromotion
    canonicalPNFHodgeResidualTopologyReceipt
  ≡
  false
canonicalReceiptHodgeDecompositionAuthorityFailClosed =
  refl

canonicalReceiptHarmonicCycleAuthorityFailClosed :
  harmonicCycleAuthorityPromotion
    canonicalPNFHodgeResidualTopologyReceipt
  ≡
  false
canonicalReceiptHarmonicCycleAuthorityFailClosed =
  refl

canonicalReceiptTopologyDecisionAuthorityFailClosed :
  topologyDecisionAuthorityPromotion
    canonicalPNFHodgeResidualTopologyReceipt
  ≡
  false
canonicalReceiptTopologyDecisionAuthorityFailClosed =
  refl

canonicalContradictionOneCellIsNegative :
  Graph.sign (graphWeight canonicalContradictionOneCell)
  ≡
  Graph.negativeResidualWeight
canonicalContradictionOneCellIsNegative =
  refl

canonicalFeatureIsClosedContradictionStructure :
  featureTag canonicalCycleFeature
  ≡
  closedContradictionStructureFeature
canonicalFeatureIsClosedContradictionStructure =
  refl

canonicalFeatureIsFrustratedSignedCycle :
  featureTag canonicalFrustratedSignedCycleFeature
  ≡
  frustratedSignedCycleFeature
canonicalFeatureIsFrustratedSignedCycle =
  refl

canonicalFeatureIsRotationalFrustration :
  featureTag canonicalRotationalFrustrationFeature
  ≡
  rotationalFrustrationFeature
canonicalFeatureIsRotationalFrustration =
  refl

canonicalFeatureIsHarmonicCycleDiagnostic :
  featureTag canonicalHarmonicCycleDiagnosticFeature
  ≡
  harmonicCycleDiagnosticFeature
canonicalFeatureIsHarmonicCycleDiagnostic =
  refl

canonicalHarmonicCycleGrantsNoHodgeAuthority :
  featureGrantsHodgeAuthority canonicalHarmonicCycleDiagnosticFeature
  ≡
  false
canonicalHarmonicCycleGrantsNoHodgeAuthority =
  refl
