module DASHI.Biology.HallHybridManifoldTreeCarrier where

open import DASHI.Core.Prelude

import DASHI.Biology.PsychedelicAttractorReweightingBoundary as Attractor
import DASHI.Geometry.SSP369Ultrametric as U369
import DASHI.Biology.LogPolarRetinotopyBridge as Retinotopy

------------------------------------------------------------------------
-- Finite hybrid smooth-chart / ultrametric-tree carrier.
--
-- The address component records hierarchical branch separation.  The chart
-- component records local continuous-like displacement.  The additive hybrid
-- metric proves that local chart motion and cross-branch transitions are
-- distinct contributions to representational distance.

data LocalChartPoint : Set where
  chartPoint0 : LocalChartPoint
  chartPoint1 : LocalChartPoint
  chartPoint2 : LocalChartPoint

chartDistance : LocalChartPoint → LocalChartPoint → Nat
chartDistance chartPoint0 chartPoint0 = 0
chartDistance chartPoint0 chartPoint1 = 1
chartDistance chartPoint0 chartPoint2 = 2
chartDistance chartPoint1 chartPoint0 = 1
chartDistance chartPoint1 chartPoint1 = 0
chartDistance chartPoint1 chartPoint2 = 1
chartDistance chartPoint2 chartPoint0 = 2
chartDistance chartPoint2 chartPoint1 = 1
chartDistance chartPoint2 chartPoint2 = 0

record HybridVisualPoint : Set where
  constructor hybridVisualPoint
  field
    branchAddress : Attractor.DepthTwoAddress
    localChart : LocalChartPoint

open HybridVisualPoint public

hybridDistance : HybridVisualPoint → HybridVisualPoint → Nat
hybridDistance x y =
  U369.distance (branchAddress x) (branchAddress y)
  +
  chartDistance (localChart x) (localChart y)

habitualChartOrigin : HybridVisualPoint
habitualChartOrigin =
  hybridVisualPoint Attractor.habitualAddress chartPoint0

habitualChartNeighbour : HybridVisualPoint
habitualChartNeighbour =
  hybridVisualPoint Attractor.habitualAddress chartPoint1

nearbyBranchOrigin : HybridVisualPoint
nearbyBranchOrigin =
  hybridVisualPoint Attractor.nearbyAddress chartPoint0

crossBranchNeighbour : HybridVisualPoint
crossBranchNeighbour =
  hybridVisualPoint Attractor.crossBranchAddress chartPoint1

localChartMoveHasDistanceOne :
  hybridDistance habitualChartOrigin habitualChartNeighbour ≡ 1
localChartMoveHasDistanceOne = refl

nearbyBranchMoveHasDistanceOne :
  hybridDistance habitualChartOrigin nearbyBranchOrigin ≡ 1
nearbyBranchMoveHasDistanceOne = refl

crossBranchAndChartMoveHasDistanceThree :
  hybridDistance habitualChartOrigin crossBranchNeighbour ≡ 3
crossBranchAndChartMoveHasDistanceThree = refl

------------------------------------------------------------------------
-- Transitions have both a branch and a chart component.

data HybridTransitionKind : Set where
  localDeformationTransition : HybridTransitionKind
  nearbyAssociationTransition : HybridTransitionKind
  crossBranchVisionTransition : HybridTransitionKind

applyHybridTransition :
  HybridTransitionKind → HybridVisualPoint → HybridVisualPoint
applyHybridTransition localDeformationTransition
  (hybridVisualPoint address chartPoint0) =
    hybridVisualPoint address chartPoint1
applyHybridTransition localDeformationTransition
  (hybridVisualPoint address chartPoint1) =
    hybridVisualPoint address chartPoint2
applyHybridTransition localDeformationTransition
  (hybridVisualPoint address chartPoint2) =
    hybridVisualPoint address chartPoint2
applyHybridTransition nearbyAssociationTransition point =
  hybridVisualPoint Attractor.nearbyAddress (localChart point)
applyHybridTransition crossBranchVisionTransition point =
  hybridVisualPoint Attractor.crossBranchAddress (localChart point)

localTransitionPreservesBranch :
  branchAddress
    (applyHybridTransition localDeformationTransition habitualChartOrigin)
  ≡
  Attractor.habitualAddress
localTransitionPreservesBranch = refl

nearbyTransitionChangesTreeComponent :
  branchAddress
    (applyHybridTransition nearbyAssociationTransition habitualChartOrigin)
  ≡
  Attractor.nearbyAddress
nearbyTransitionChangesTreeComponent = refl

crossBranchTransitionChangesTreeComponent :
  branchAddress
    (applyHybridTransition crossBranchVisionTransition habitualChartOrigin)
  ≡
  Attractor.crossBranchAddress
crossBranchTransitionChangesTreeComponent = refl

------------------------------------------------------------------------
-- Surface-far/root-near underdetermination.

data SemanticRoot : Set where
  architecturalRoot : SemanticRoot
  biologicalRoot : SemanticRoot

semanticRoot : HybridVisualPoint → SemanticRoot
semanticRoot point = architecturalRoot

sameRootCanHaveNonzeroHybridDistance :
  semanticRoot habitualChartOrigin
  ≡
  semanticRoot habitualChartNeighbour
  ×
  hybridDistance habitualChartOrigin habitualChartNeighbour ≡ 1
sameRootCanHaveNonzeroHybridDistance = refl , refl

------------------------------------------------------------------------
-- Retinotopic projection is a consumer, not an inverse of the hybrid carrier.

projectHybridGenerator : HybridVisualPoint → Retinotopy.CorticalPattern
projectHybridGenerator point with U369.distance
  (branchAddress point) Attractor.habitualAddress
... | zero = Retinotopy.radialTunnelPattern
... | suc zero = Retinotopy.radialTunnelPattern
... | suc (suc n) = Retinotopy.branchingPattern

habitualAndNearbyProjectTogether :
  projectHybridGenerator habitualChartOrigin
  ≡
  projectHybridGenerator nearbyBranchOrigin
habitualAndNearbyProjectTogether = refl

record HybridCarrierBoundary : Set where
  constructor hybridCarrierBoundary
  field
    treeDistanceAloneIsCompleteGeometry : Bool
    treeDistanceAloneIsCompleteGeometryIsFalse :
      treeDistanceAloneIsCompleteGeometry ≡ false

    chartDistanceAloneIsCompleteGeometry : Bool
    chartDistanceAloneIsCompleteGeometryIsFalse :
      chartDistanceAloneIsCompleteGeometry ≡ false

    corticalProjectionInvertsHybridState : Bool
    corticalProjectionInvertsHybridStateIsFalse :
      corticalProjectionInvertsHybridState ≡ false

open HybridCarrierBoundary public

canonicalHybridCarrierBoundary : HybridCarrierBoundary
canonicalHybridCarrierBoundary =
  hybridCarrierBoundary false refl false refl false refl
