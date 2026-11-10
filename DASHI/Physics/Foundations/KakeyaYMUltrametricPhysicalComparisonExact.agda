{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.KakeyaYMUltrametricPhysicalComparisonExact where

------------------------------------------------------------------------
-- KAKeya x YM x ORIGINAL PADIC/HYPERMETRIC PRIOR ART
--
-- Reuse BalabanRGTwoMetricUniformComparisonExact instead of re-proving
-- metric-contraction algebra. Reuse TernaryCylinderPantsGeometryExact
-- and ContextDependentPadicPhysicalMapExact as exact negative controls.
--
-- Key distinction: a scale-covariant RG address metric and a physical
-- metric are two selected metrics. A 3D voxel observation of a triadic
-- cylinder is not by itself an isometric Euclidean realisation.
--
-- Sources: Wang and Zahl (2025, arXiv:2502.17655);
-- Guth, Wang and Zahl (2026, arXiv:2601.14411);
-- original DASHI RG/ultrametric/physical projection theorem owners.
-- This is a conditional finite metric *inequality*, not a Kakeya
-- dimension theorem or a physical metric-construction certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_; _+_; _≤_)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.YangMills.BalabanRGTwoMetricUniformComparisonExact as RG
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants
import DASHI.Biology.Physical.ContextDependentPadicPhysicalMapExact as Context

-- This source theorem already composes two-metric comparisons with a
-- contraction and reopening error. It works for selected rational
-- distances, without silently asserting the comparison constants.
sameSelectedPhysicalMetricBound :
  (step : RG.RGTwoMetricStep) →
  RG.comparisonLower step * RG.physicalDistanceNext step
  ≤ RG.contraction step * RG.comparisonUpper step
      * RG.physicalDistance step
    + RG.physicalScale step * RG.reopeningError step
sameSelectedPhysicalMetricBound =
  RG.rgContractionTransfersToPhysicalMetric

-- The original 3D voxel image is *expressly* an extrinsic observation,
-- not an isometry of the p-adic cylinder ultrametric.
canonicalVoxelIsometryIsNotClaimed :
  Pants.voxelEmbeddingIsUltrametricIsometry
    Pants.canonicalTernaryPantsGeometryBoundary ≡ false
canonicalVoxelIsometryIsNotClaimed =
  Pants.voxelEmbeddingIsUltrametricIsometryIsFalse
    Pants.canonicalTernaryPantsGeometryBoundary

-- Context affects the downstream physical parameter even for the same
-- exact fine address. Therefore an address-only physical projection
-- cannot be inferred from the ultrametric distance itself.
sameAddressContextDependence :
  Context.contextualParameter
    Context.closedContext
    Context.Base.fineA
  ≡ Context.contextualParameter
    Context.openContext
    Context.Base.fineA
  → Context.⊥
sameAddressContextDependence =
  Context.sameFineAddressDifferentContextChangesParameter

-- The correct input to the original Kakeya/YM spatial bridge is therefore
-- a selected physical metric comparison, not a bare ternary address code.
-- Even a proven two-sided metric comparison transports metric coverings
-- only after a complete, all-scales real/Borel interpretation is supplied;
-- Euclidean line segments require additional line-preservation proof.

record OriginalMetricComparisonRequirements : Set₁ where
  field
    SpatialState : Set
    AddressState : Set
    observeAddress : SpatialState → AddressState
    physicalDistance : SpatialState → SpatialState → ℚ
    rgDistance : AddressState → AddressState → ℚ
    physicalScale : ℚ
    lowerConstant upperConstant : ℚ
    -- There are deliberately no fabricated inhabitants of these
    -- source-level comparison obligations.
    lowerComparison :
      ∀ x y →
      lowerConstant * physicalDistance x y
      ≤ physicalScale *
        rgDistance (observeAddress x) (observeAddress y)
    upperComparison :
      ∀ x y →
      physicalScale *
        rgDistance (observeAddress x) (observeAddress y)
      ≤ upperConstant * physicalDistance x y

open OriginalMetricComparisonRequirements public

-- The constant-comparison statement is an exact definitional
-- consumption of the same selected original physical carrier.
selectedMetricUpperComparison :
  (requirements : OriginalMetricComparisonRequirements) →
  ∀ x y →
  physicalScale requirements *
    rgDistance requirements
      (observeAddress requirements x)
      (observeAddress requirements y)
  ≤ upperConstant requirements *
    physicalDistance requirements x y
selectedMetricUpperComparison requirements =
  upperComparison requirements

selectedMetricLowerComparison :
  (requirements : OriginalMetricComparisonRequirements) →
  ∀ x y →
  lowerConstant requirements * physicalDistance requirements x y
  ≤ physicalScale requirements *
    rgDistance requirements
      (observeAddress requirements x)
      (observeAddress requirements y)
selectedMetricLowerComparison requirements =
  lowerComparison requirements

physicalKakeyaTransportClosedHere : Bool
physicalKakeyaTransportClosedHere = false

physicalKakeyaTransportClosedHereIsFalse :
  physicalKakeyaTransportClosedHere ≡ false
physicalKakeyaTransportClosedHereIsFalse = refl
