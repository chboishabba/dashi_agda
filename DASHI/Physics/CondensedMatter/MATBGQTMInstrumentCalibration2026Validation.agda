module DASHI.Physics.CondensedMatter.MATBGQTMInstrumentCalibration2026Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGQTMInstrumentCalibration2026Exact as Q

sample-calibration-source-paid : Q.sampleGeometrySourcePaid Q.canonicalQTMInstrumentCalibrationBoundary ≡ true
sample-calibration-source-paid = refl

observer-resolution-source-paid : Q.observerResolutionSourcePaid Q.canonicalQTMInstrumentCalibrationBoundary ≡ true
observer-resolution-source-paid = refl

instrument-calibration-is-not-qtm-array-replay : Q.calibrationCreatesExperimentalIntensityArrays Q.canonicalQTMInstrumentCalibrationBoundary ≡ false
instrument-calibration-is-not-qtm-array-replay = refl

instrument-calibration-is-not-quantum-metric-measurement : Q.calibrationCreatesMeasuredQuantumMetric Q.canonicalQTMInstrumentCalibrationBoundary ≡ false
instrument-calibration-is-not-quantum-metric-measurement = refl
