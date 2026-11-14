module DASHI.Physics.QuantumSensors.NVDiscreteGaugeCurvatureBridgeExact where

-- Finite triangle gauge curvature -> calibrated axial-field coefficient
-- -> symbolic NV resonance. This is a concrete compositional toy model,
-- NOT a continuum Maxwell solver, a 4+1 Einstein reduction, or observed ODMR.
-- Physical NV spin-one Zeeman model: established background physics.
-- Discrete cochains/gauge cancellation: classical mathematics.
-- Source-written implementation: DASHI, based on #1238 and sibling #1239.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Rational.Base using (ℚ; _+_; _*_)
import DASHI.Physics.Measurement.BioEMDiscreteCurvatureGaugeExact as G
import DASHI.Physics.QuantumSensors.NVSpinOneAxialExact as NV
import DASHI.Physics.QuantumSensors.NVFiniteResonanceReadoutExact as R
import DASHI.Algebra.Quantum.FiniteQutrit as Q

record FiniteCurvatureNV : Set where
  constructor curvature-nv
  field
    sensorGain : ℚ
    backgroundField : ℚ
    zeroFieldSplitting : ℚ
    gyromagneticRatio : ℚ
    microwaveReference : ℚ
open FiniteCurvatureNV public

fieldFromTriangle : FiniteCurvatureNV → G.TrianglePotential → ℚ
fieldFromTriangle p a =
  sensorGain p * G.curvature a + backgroundField p

modelFromTriangle : FiniteCurvatureNV → G.TrianglePotential → NV.AxialNV
modelFromTriangle p a = NV.axial-nv
  (zeroFieldSplitting p) (gyromagneticRatio p)
  (fieldFromTriangle p a)

resonanceFromTriangle : FiniteCurvatureNV → G.TrianglePotential → R.SymbolicODMRDatum
resonanceFromTriangle p a =
  R.predictODMR
    (R.finite-resonance (modelFromTriangle p a) (microwaveReference p))

fieldGaugeInvariant :
  (p : FiniteCurvatureNV) (chi : G.VertexGauge)
  (a : G.TrianglePotential) →
  fieldFromTriangle p (G.gaugeShift chi a) ≡ fieldFromTriangle p a
fieldGaugeInvariant p chi a =
  cong (λ f → sensorGain p * f + backgroundField p)
       (G.gaugeInvariantCurvature chi a)

resonanceGaugeInvariant :
  (p : FiniteCurvatureNV) (chi : G.VertexGauge)
  (a : G.TrianglePotential) →
  resonanceFromTriangle p (G.gaugeShift chi a) ≡
  resonanceFromTriangle p a
resonanceGaugeInvariant p chi a =
  cong (λ b →
    R.predictODMR
      (R.finite-resonance
        (NV.axial-nv (zeroFieldSplitting p) (gyromagneticRatio p) b)
        (microwaveReference p)))
       (fieldGaugeInvariant p chi a)

-- A gauge-invariant prediction does not yield a complete inverse or
-- measured-photon likelihood without separately supplied model assumptions.
