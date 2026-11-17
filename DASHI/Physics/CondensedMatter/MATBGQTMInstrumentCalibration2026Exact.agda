module DASHI.Physics.CondensedMatter.MATBGQTMInstrumentCalibration2026Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- XIAO ET AL. 2026 SAME-REGION QTM / SAMPLE CALIBRATION
--
-- Source: Nature 653 (2026), DOI 10.1038/s41586-026-10378-x,
-- Methods / Extended Data Figs. 1-2.
--
-- These values calibrate sample geometry and the observer resolution. They do
-- not provide the experimental intensity arrays, an interacting QTM fit, or a
-- measured quantum metric.
------------------------------------------------------------------------

record QTMInstrumentCalibrationReceipt : Set where
  constructor qtm-instrument-calibration-receipt
  field
    sourceDOI : String
    moireVector1Nm : String
    moireVector2Nm : String
    moireVector3Nm : String
    twistAngleDeg : String
    twistAngleUncertaintyDeg : String
    heterostrainPercent : String
    heterostrainUncertaintyPercent : String
    tipFootprintNm : String
    expectedAngularResolutionPrincipal1Deg : String
    expectedAngularResolutionPrincipal2Deg : String
    observedRemoteBandAngularFWHMDeg : String
    observedMomentumResolutionInvNm : String
    energyResolutionUpperBoundMeV : String

open QTMInstrumentCalibrationReceipt public

canonicalQTMInstrumentCalibrationReceipt : QTMInstrumentCalibrationReceipt
canonicalQTMInstrumentCalibrationReceipt =
  qtm-instrument-calibration-receipt
    "10.1038/s41586-026-10378-x"
    "12.72"
    "12.73"
    "13.14"
    "1.10"
    "0.02"
    "0.03"
    "0.02"
    "50 x 200"
    "0.05"
    "0.2"
    "0.1"
    "0.03"
    "10"

record QTMInstrumentCalibrationBoundary : Set where
  constructor qtm-instrument-calibration-boundary
  field
    sampleGeometrySourcePaid : Bool
    observerResolutionSourcePaid : Bool
    calibrationCreatesExperimentalIntensityArrays : Bool
    calibrationCreatesInteractingQTMFit : Bool
    calibrationCreatesMeasuredQuantumMetric : Bool
    calibrationCreatesSameSampleEntropyIdentity : Bool

open QTMInstrumentCalibrationBoundary public

canonicalQTMInstrumentCalibrationBoundary : QTMInstrumentCalibrationBoundary
canonicalQTMInstrumentCalibrationBoundary =
  qtm-instrument-calibration-boundary
    true true false false false false
