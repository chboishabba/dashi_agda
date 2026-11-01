module DASHI.Geometry.CausalRelationalMetricSelector where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Geometry.ValuationConformalMetricCandidate as Valuation

------------------------------------------------------------------------
-- Typed augmentation of a scalar valuation.
--
-- A scalar valuation can supply a depth/scale profile, but it cannot select a
-- causal direction or orientation.  This module adds the missing typed data:
--
--   valuation profile
--   + causal role assignment
--   + pairwise relational table
--   + spatial orientation
--   --------------------------------
--   selected oriented Lorentzian metric table.
--
-- The finite selector is exact for the canonical Axis4 model.  It is not a
-- derivation of physical spacetime or a replacement for smooth metric theory.


data SpatialOrientation : Set where
  rightHanded : SpatialOrientation
  leftHanded : SpatialOrientation


data AxisRole : Set where
  causalTime : AxisRole
  spatialDirection : AxisRole


data AxisRelation : Set where
  sameDirection : AxisRelation
  orthogonalDirections : AxisRelation


canonicalAxisRole : Flat.Axis4 → AxisRole
canonicalAxisRole Flat.timeAxis = causalTime
canonicalAxisRole Flat.xAxis = spatialDirection
canonicalAxisRole Flat.yAxis = spatialDirection
canonicalAxisRole Flat.zAxis = spatialDirection


canonicalAxisRelation : Flat.Axis4 → Flat.Axis4 → AxisRelation
canonicalAxisRelation Flat.timeAxis Flat.timeAxis = sameDirection
canonicalAxisRelation Flat.timeAxis Flat.xAxis = orthogonalDirections
canonicalAxisRelation Flat.timeAxis Flat.yAxis = orthogonalDirections
canonicalAxisRelation Flat.timeAxis Flat.zAxis = orthogonalDirections
canonicalAxisRelation Flat.xAxis Flat.timeAxis = orthogonalDirections
canonicalAxisRelation Flat.xAxis Flat.xAxis = sameDirection
canonicalAxisRelation Flat.xAxis Flat.yAxis = orthogonalDirections
canonicalAxisRelation Flat.xAxis Flat.zAxis = orthogonalDirections
canonicalAxisRelation Flat.yAxis Flat.timeAxis = orthogonalDirections
canonicalAxisRelation Flat.yAxis Flat.xAxis = orthogonalDirections
canonicalAxisRelation Flat.yAxis Flat.yAxis = sameDirection
canonicalAxisRelation Flat.yAxis Flat.zAxis = orthogonalDirections
canonicalAxisRelation Flat.zAxis Flat.timeAxis = orthogonalDirections
canonicalAxisRelation Flat.zAxis Flat.xAxis = orthogonalDirections
canonicalAxisRelation Flat.zAxis Flat.yAxis = orthogonalDirections
canonicalAxisRelation Flat.zAxis Flat.zAxis = sameDirection


canonicalRelationSymmetric :
  (a b : Flat.Axis4) →
  canonicalAxisRelation a b ≡ canonicalAxisRelation b a
canonicalRelationSymmetric Flat.timeAxis Flat.timeAxis = refl
canonicalRelationSymmetric Flat.timeAxis Flat.xAxis = refl
canonicalRelationSymmetric Flat.timeAxis Flat.yAxis = refl
canonicalRelationSymmetric Flat.timeAxis Flat.zAxis = refl
canonicalRelationSymmetric Flat.xAxis Flat.timeAxis = refl
canonicalRelationSymmetric Flat.xAxis Flat.xAxis = refl
canonicalRelationSymmetric Flat.xAxis Flat.yAxis = refl
canonicalRelationSymmetric Flat.xAxis Flat.zAxis = refl
canonicalRelationSymmetric Flat.yAxis Flat.timeAxis = refl
canonicalRelationSymmetric Flat.yAxis Flat.xAxis = refl
canonicalRelationSymmetric Flat.yAxis Flat.yAxis = refl
canonicalRelationSymmetric Flat.yAxis Flat.zAxis = refl
canonicalRelationSymmetric Flat.zAxis Flat.timeAxis = refl
canonicalRelationSymmetric Flat.zAxis Flat.xAxis = refl
canonicalRelationSymmetric Flat.zAxis Flat.yAxis = refl
canonicalRelationSymmetric Flat.zAxis Flat.zAxis = refl


record MetricSelectionData : Set where
  constructor mkMetricSelectionData
  field
    selectionLabel : String
    valuationProfile : Valuation.ValuationProfile
    spatialOrientation : SpatialOrientation
    axisRole : Flat.Axis4 → AxisRole
    axisRelation : Flat.Axis4 → Flat.Axis4 → AxisRelation
    timeRoleReceipt : axisRole Flat.timeAxis ≡ causalTime
    xRoleReceipt : axisRole Flat.xAxis ≡ spatialDirection
    yRoleReceipt : axisRole Flat.yAxis ≡ spatialDirection
    zRoleReceipt : axisRole Flat.zAxis ≡ spatialDirection
    relationSymmetric :
      (a b : Flat.Axis4) → axisRelation a b ≡ axisRelation b a
    selectionScope : String

open MetricSelectionData public


selectedMetricEntry :
  MetricSelectionData → Flat.Axis4 → Flat.Axis4 → TriTruth
selectedMetricEntry input a b with axisRelation input a b
... | orthogonalDirections = tri-mid
... | sameDirection with axisRole input a
...   | causalTime = tri-low
...   | spatialDirection = tri-high


record OrientedLorentzianSelection : Set where
  constructor mkOrientedLorentzianSelection
  field
    selectionInput : MetricSelectionData
    selectedMetric : Flat.Axis4 → Flat.Axis4 → TriTruth
    selectedMetricComputed :
      (a b : Flat.Axis4) →
      selectedMetric a b ≡ selectedMetricEntry selectionInput a b
    selectedSpatialOrientation : SpatialOrientation
    selectedValuationProfile : Valuation.ValuationProfile
    orientedSelectionScope : String

open OrientedLorentzianSelection public


selectOrientedLorentzian :
  MetricSelectionData → OrientedLorentzianSelection
selectOrientedLorentzian input =
  mkOrientedLorentzianSelection
    input
    (selectedMetricEntry input)
    (λ _ _ → refl)
    (spatialOrientation input)
    (valuationProfile input)
    "metric is selected only after valuation, causal roles, relations, and orientation are all supplied"


canonicalMetricSelectionData : MetricSelectionData
canonicalMetricSelectionData =
  mkMetricSelectionData
    "canonical-right-handed-causal-frame"
    Valuation.uniformSaturatedProfile
    rightHanded
    canonicalAxisRole
    canonicalAxisRelation
    refl refl refl refl
    canonicalRelationSymmetric
    "finite Axis4 selector; orientation is retained separately because a metric alone does not encode handedness"


canonicalOrientedLorentzianSelection : OrientedLorentzianSelection
canonicalOrientedLorentzianSelection =
  selectOrientedLorentzian canonicalMetricSelectionData


canonicalSelectedMetricMatchesFlat :
  (a b : Flat.Axis4) →
  selectedMetricEntry canonicalMetricSelectionData a b
  ≡ Flat.flatMetricEntry a b
canonicalSelectedMetricMatchesFlat Flat.timeAxis Flat.timeAxis = refl
canonicalSelectedMetricMatchesFlat Flat.timeAxis Flat.xAxis = refl
canonicalSelectedMetricMatchesFlat Flat.timeAxis Flat.yAxis = refl
canonicalSelectedMetricMatchesFlat Flat.timeAxis Flat.zAxis = refl
canonicalSelectedMetricMatchesFlat Flat.xAxis Flat.timeAxis = refl
canonicalSelectedMetricMatchesFlat Flat.xAxis Flat.xAxis = refl
canonicalSelectedMetricMatchesFlat Flat.xAxis Flat.yAxis = refl
canonicalSelectedMetricMatchesFlat Flat.xAxis Flat.zAxis = refl
canonicalSelectedMetricMatchesFlat Flat.yAxis Flat.timeAxis = refl
canonicalSelectedMetricMatchesFlat Flat.yAxis Flat.xAxis = refl
canonicalSelectedMetricMatchesFlat Flat.yAxis Flat.yAxis = refl
canonicalSelectedMetricMatchesFlat Flat.yAxis Flat.zAxis = refl
canonicalSelectedMetricMatchesFlat Flat.zAxis Flat.timeAxis = refl
canonicalSelectedMetricMatchesFlat Flat.zAxis Flat.xAxis = refl
canonicalSelectedMetricMatchesFlat Flat.zAxis Flat.yAxis = refl
canonicalSelectedMetricMatchesFlat Flat.zAxis Flat.zAxis = refl


canonicalTimeSelectedTimelike :
  selectedMetricEntry
    canonicalMetricSelectionData
    Flat.timeAxis
    Flat.timeAxis
  ≡ tri-low
canonicalTimeSelectedTimelike = refl


canonicalSpatialSelectedPositive :
  selectedMetricEntry
    canonicalMetricSelectionData
    Flat.zAxis
    Flat.zAxis
  ≡ tri-high
canonicalSpatialSelectedPositive = refl


canonicalOrthogonalSelectedZero :
  selectedMetricEntry
    canonicalMetricSelectionData
    Flat.timeAxis
    Flat.xAxis
  ≡ tri-mid
canonicalOrthogonalSelectedZero = refl
