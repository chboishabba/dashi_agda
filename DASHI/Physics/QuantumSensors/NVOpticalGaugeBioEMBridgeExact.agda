module DASHI.Physics.QuantumSensors.NVOpticalGaugeBioEMBridgeExact where

-- Exact finite observation transport:
-- vertex-gauge potential -> triangle curvature -> magnetic coefficient
-- -> spin-one labelled frequencies -> optically expected photon mean.
-- This proves only *gauge invariance* of the finite model; not a
-- quantitative or experimentally calibrated optical readout.

open import Agda.Builtin.Equality using (_≡_; cong)
open import Data.Rational.Base using (ℚ)
import DASHI.Physics.Measurement.BioEMDiscreteCurvatureGaugeExact as Gauge
import DASHI.Physics.QuantumSensors.NVDiscreteGaugeCurvatureBridgeExact as NV
import DASHI.Physics.QuantumSensors.NVOpticalPhotonReadoutExact as Optical

predictedOpticalMean :
  NV.FiniteCurvatureNV → Optical.OpticalNVTransfer →
  Gauge.TrianglePotential → ℚ
predictedOpticalMean p o a =
  Optical.predictPhotonMean o (NV.resonanceFromTriangle p a)

opticalGaugeInvariant :
  (p : NV.FiniteCurvatureNV) (o : Optical.OpticalNVTransfer)
  (chi : Gauge.VertexGauge) (a : Gauge.TrianglePotential) →
  predictedOpticalMean p o (Gauge.gaugeShift chi a) ≡
  predictedOpticalMean p o a
opticalGaugeInvariant p o chi a =
  cong (Optical.predictPhotonMean o)
       (NV.resonanceGaugeInvariant p chi a)

-- Neither expected photon count nor magnetometry sensitivity is an
-- observational equality with measured data without a calibration receipt.
