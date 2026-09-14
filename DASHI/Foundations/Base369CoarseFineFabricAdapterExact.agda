module DASHI.Foundations.Base369CoarseFineFabricAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369NDimParetoChartExact as Chart

------------------------------------------------------------------------
-- BASE369 -> CANONICAL COARSE / RELATIVE-FINE REOPENING
------------------------------------------------------------------------

base369CoarseFineReopening :
  Fibre.CoarseFineReopening Geometry.TernaryHyperformalPoint
base369CoarseFineReopening =
  Fibre.coarseFineReopening
    Geometry.Ternary27Point
    Geometry.AppraisalFibrePoint
    Geometry.projectInteractionVoxel
    Geometry.projectAppraisalFibre
    Geometry.rebuildOverInteraction
    (λ { (Geometry.ternaryHyperformalPoint interaction appraisalA appraisalB) → refl })

base369CoarseFineObserver :
  Geometry.TernaryHyperformalPoint →
  Geometry.Ternary27Point × Geometry.AppraisalFibrePoint
base369CoarseFineObserver =
  Fibre.coarseFineObserver base369CoarseFineReopening

base369CoarseFineObserverSeparating :
  (left right : Geometry.TernaryHyperformalPoint) →
  base369CoarseFineObserver left ≡ base369CoarseFineObserver right →
  left ≡ right
base369CoarseFineObserverSeparating =
  Fibre.coarseFineObserverSeparating base369CoarseFineReopening

base369InteractionPlusAppraisalDeterminesState :
  {left right : Geometry.TernaryHyperformalPoint} →
  Geometry.projectInteractionVoxel left ≡ Geometry.projectInteractionVoxel right →
  Geometry.projectAppraisalFibre left ≡ Geometry.projectAppraisalFibre right →
  left ≡ right
base369InteractionPlusAppraisalDeterminesState =
  Fibre.coarseAndRelativeFineDetermineState base369CoarseFineReopening

record Base369CoarseFineBoundary : Set where
  constructor base369CoarseFineBoundary
  field
    exactCoarseFineReopeningAvailable : Bool
    interactionVoxelIsCoarseCoordinate : Bool
    appraisalPairIsRelativeFineCoordinate : Bool
    appraisalFibreHas729States : Bool
    fullFabricHas19683States : Bool
    profileCountEqualsParetoDimension : Bool
    base369IsGenericFabric : Bool

canonicalBase369CoarseFineBoundary : Base369CoarseFineBoundary
canonicalBase369CoarseFineBoundary =
  base369CoarseFineBoundary true true true true true false false

existingGeometryBoundary : Geometry.Ternary27HypervoxelGeometryBoundary
existingGeometryBoundary = Geometry.canonicalTernary27HypervoxelGeometryBoundary

existingNDimChartBoundary : Chart.Base369NDimParetoChartBoundary
existingNDimChartBoundary = Chart.canonicalBase369NDimParetoChartBoundary
