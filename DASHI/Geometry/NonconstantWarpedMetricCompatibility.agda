module DASHI.Geometry.NonconstantWarpedMetricCompatibility where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Geometry.NonconstantWarpedLorentzianModel as Geometry

------------------------------------------------------------------------
-- Model-specific discrete metric-compatibility computation.
--
-- For the normalized warped frame, the spatial metric log-gradient H and the
-- corresponding Gamma^0_ii coefficient must agree.  The residual is computed
-- with the same signed-difference operation used by the geometry model.
--
-- This is a finite compatibility equation for the selected coefficient table,
-- not the general smooth identity nabla g = 0.


data SpatialAxis : Set where
  spatialX : SpatialAxis
  spatialY : SpatialAxis
  spatialZ : SpatialAxis


embedSpatial : SpatialAxis → Flat.Axis4
embedSpatial spatialX = Flat.xAxis
embedSpatial spatialY = Flat.yAxis
embedSpatial spatialZ = Flat.zAxis


metricLogGradient :
  Geometry.TimeEdge → SpatialAxis → Geometry.UnitCoefficient
metricLogGradient edge spatial = Geometry.hubbleCoefficient edge


connectionMetricGradient :
  Geometry.TimeEdge → SpatialAxis → Geometry.UnitCoefficient
connectionMetricGradient edge spatial =
  Geometry.leviCivitaCoefficient
    edge
    Flat.timeAxis
    (embedSpatial spatial)
    (embedSpatial spatial)


metricCompatibilityResidual :
  Geometry.TimeEdge → SpatialAxis → Geometry.UnitCoefficient
metricCompatibilityResidual edge spatial =
  Geometry.unitDifference
    (metricLogGradient edge spatial)
    (connectionMetricGradient edge spatial)


pastXCompatibility :
  metricCompatibilityResidual Geometry.pastToPresent spatialX
  ≡ Geometry.zeroUnit
pastXCompatibility = refl


pastYCompatibility :
  metricCompatibilityResidual Geometry.pastToPresent spatialY
  ≡ Geometry.zeroUnit
pastYCompatibility = refl


pastZCompatibility :
  metricCompatibilityResidual Geometry.pastToPresent spatialZ
  ≡ Geometry.zeroUnit
pastZCompatibility = refl


futureXCompatibility :
  metricCompatibilityResidual Geometry.presentToFuture spatialX
  ≡ Geometry.zeroUnit
futureXCompatibility = refl


futureYCompatibility :
  metricCompatibilityResidual Geometry.presentToFuture spatialY
  ≡ Geometry.zeroUnit
futureYCompatibility = refl


futureZCompatibility :
  metricCompatibilityResidual Geometry.presentToFuture spatialZ
  ≡ Geometry.zeroUnit
futureZCompatibility = refl


computedMetricCompatibility :
  (edge : Geometry.TimeEdge) →
  (spatial : SpatialAxis) →
  metricCompatibilityResidual edge spatial ≡ Geometry.zeroUnit
computedMetricCompatibility Geometry.pastToPresent spatialX = refl
computedMetricCompatibility Geometry.pastToPresent spatialY = refl
computedMetricCompatibility Geometry.pastToPresent spatialZ = refl
computedMetricCompatibility Geometry.presentToFuture spatialX = refl
computedMetricCompatibility Geometry.presentToFuture spatialY = refl
computedMetricCompatibility Geometry.presentToFuture spatialZ = refl


record ComputedWarpedMetricCompatibilityReceipt : Set where
  constructor mkComputedWarpedMetricCompatibilityReceipt
  field
    residualComputedZero :
      (edge : Geometry.TimeEdge) →
      (spatial : SpatialAxis) →
      metricCompatibilityResidual edge spatial ≡ Geometry.zeroUnit
    sourceCoefficientNonzero :
      connectionMetricGradient Geometry.pastToPresent spatialX
      ≡ Geometry.positiveUnit
    receiptScope : String

open ComputedWarpedMetricCompatibilityReceipt public


computedWarpedMetricCompatibilityReceipt :
  ComputedWarpedMetricCompatibilityReceipt
computedWarpedMetricCompatibilityReceipt =
  mkComputedWarpedMetricCompatibilityReceipt
    computedMetricCompatibility
    refl
    "finite normalized metric-compatibility residual computed from metric gradients and connection coefficients"
