module DASHI.Physics.Measurement.BioEMDiscreteCurvatureGaugeExact where

-- Exact simplicial edge-cochain gauge model on one oriented triangle.
-- The sum of potential shifts around the triangle vanishes (d^2 = 0).
-- This is a finite combinatorial curvature witness, not an analytic
-- Maxwell solution, nor the KK Ricci reduction.
-- Classical provenance: gauge theory / simplicial cohomology.
-- DASHI contribution: explicit source-to-observable consumer bridge.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Measurement.CausalBioelectromagneticExperimentExact as Bio

record TrianglePotential : Set where
  constructor triangle
  field
    edge01 edge12 edge20 : ℚ
open TrianglePotential public

record VertexGauge : Set where
  constructor vertices
  field
    value0 value1 value2 : ℚ
open VertexGauge public

gaugeShift : VertexGauge → TrianglePotential → TrianglePotential
gaugeShift v a = triangle
  (edge01 a + (value1 v - value0 v))
  (edge12 a + (value2 v - value1 v))
  (edge20 a + (value0 v - value2 v))

curvature : TrianglePotential → ℚ
curvature a = edge01 a + edge12 a + edge20 a

gaugeInvariantCurvature :
  (v : VertexGauge) (a : TrianglePotential) →
  curvature (gaugeShift v a) ≡ curvature a
gaugeInvariantCurvature (vertices x y z) (triangle a b c) =
  solve (x ∷ y ∷ z ∷ a ∷ b ∷ c ∷ [])

record RationalMagneticReadout : Set where
  constructor rational-readout
  field
    gain offset : ℚ
open RationalMagneticReadout public

observe : RationalMagneticReadout → TrianglePotential → ℚ
observe device a = gain device + curvature a + offset device

readoutGaugeInvariant :
  (device : RationalMagneticReadout)
  (v : VertexGauge) (a : TrianglePotential) →
  observe device (gaugeShift v a) ≡ observe device a
readoutGaugeInvariant device v a =
  cong (λ flux → gain device + flux + offset device)
       (gaugeInvariantCurvature v a)
