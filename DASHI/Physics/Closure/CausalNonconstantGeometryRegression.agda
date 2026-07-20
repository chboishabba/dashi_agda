module DASHI.Physics.Closure.CausalNonconstantGeometryRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

import Base369 as B369
import DASHI.Geometry.CausalRelationalMetricSelector as Selector
import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Geometry.NonconstantWarpedLorentzianModel as Geometry
import DASHI.Geometry.NonconstantWarpedMetricCompatibility as Compatibility
import DASHI.Physics.Closure.DiscreteWarpedEinsteinMatterModel as Matter
import DASHI.Physics.Closure.StressEnergyBianchiConditional as Boundary

------------------------------------------------------------------------
-- Compact regression surface for the augmented causal/nonconstant tranche.


selectedTimeMetricRegression :
  Selector.selectedMetricEntry
    Selector.canonicalMetricSelectionData
    Flat.timeAxis
    Flat.timeAxis
  ≡ B369.tri-low
selectedTimeMetricRegression = Selector.canonicalTimeSelectedTimelike


selectedMetricMatchesFlatRegression :
  (a b : Flat.Axis4) →
  Selector.selectedMetricEntry Selector.canonicalMetricSelectionData a b
  ≡ Flat.flatMetricEntry a b
selectedMetricMatchesFlatRegression = Selector.canonicalSelectedMetricMatchesFlat


metricActuallyChangesRegression :
  Geometry.DepthChange
    (Geometry.logarithmicScaleDepth
      (Geometry.localMetricEntry Geometry.pastSlice Flat.xAxis Flat.xAxis))
    (Geometry.logarithmicScaleDepth
      (Geometry.localMetricEntry Geometry.presentSlice Flat.xAxis Flat.xAxis))
metricActuallyChangesRegression = Geometry.pastPresentMetricChanges


computedConnectionRegression :
  Geometry.leviCivitaCoefficient
    Geometry.pastToPresent
    Flat.timeAxis
    Flat.xAxis
    Flat.xAxis
  ≡ Geometry.positiveUnit
computedConnectionRegression = Geometry.computedConnectionNonzero


computedTorsionFreeRegression :
  (edge : Geometry.TimeEdge) →
  (upper lower₁ lower₂ : Flat.Axis4) →
  Geometry.leviCivitaCoefficient edge upper lower₁ lower₂
  ≡ Geometry.leviCivitaCoefficient edge upper lower₂ lower₁
computedTorsionFreeRegression = Geometry.leviCivitaLowerSymmetric


computedMetricCompatibilityRegression :
  (edge : Geometry.TimeEdge) →
  (spatial : Compatibility.SpatialAxis) →
  Compatibility.metricCompatibilityResidual edge spatial
  ≡ Geometry.zeroUnit
computedMetricCompatibilityRegression =
  Compatibility.computedMetricCompatibility


computedCurvatureRegression :
  Geometry.warpedSectionalCurvature ≡ Geometry.positiveCurvature
computedCurvatureRegression = Geometry.computedPositiveCurvature


computedNonzeroSourceRegression :
  Matter.computedMatterStress Flat.timeAxis Flat.timeAxis
  ≡ Matter.positiveSource
computedNonzeroSourceRegression = Matter.computedMatterSourceNonzero


computedEinsteinSourceRegression :
  (a b : Flat.Axis4) →
  Matter.computedEinsteinTensor a b ≡ Matter.computedMatterStress a b
computedEinsteinSourceRegression = Matter.computedEinsteinEqualsMatterStress


computedBianchiRegression :
  Matter.continuityBianchiResidual ≡ Matter.zeroSource
computedBianchiRegression = Matter.computedContractedBianchi


residueEnergyMassShortcutBlockedRegression :
  Boundary.ionizationStyleEnergyIdentifiedWithMass
    Boundary.canonicalMassIdentificationBoundary
  ≡ false
residueEnergyMassShortcutBlockedRegression =
  Boundary.canonicalResidueEnergyNotMass
