module DASHI.Physics.CondensedMatter.MATBGQuantumGeometryReplayValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGQuantumGeometryReplayReceiptExact as Geometry

projectorGeometryExecutionPaid : Geometry.projectorGeometryExecutionPaid Geometry.canonicalQuantumGeometryBoundary ≡ true
projectorGeometryExecutionPaid = refl

shellConvergencePaid : Geometry.shell3To4MetricConvergencePaid Geometry.canonicalQuantumGeometryBoundary ≡ true
shellConvergencePaid = refl

metricInhomogeneityObservedNumerically : Geometry.coarseMetricInhomogeneityPaid Geometry.canonicalQuantumGeometryBoundary ≡ true
metricInhomogeneityObservedNumerically = refl

experimentalMetricCalibrationStillFalse : Geometry.experimentalQuantumMetricCalibrationPaid Geometry.canonicalQuantumGeometryBoundary ≡ false
experimentalMetricCalibrationStillFalse = refl

localScanDoesNotCreateChernNumber : Geometry.chernNumberPaid Geometry.canonicalQuantumGeometryBoundary ≡ false
localScanDoesNotCreateChernNumber = refl
