module DASHI.Physics.Measurement.BioEMGaugeFibreBoundaryExact where

-- Gauge/extra-coordinate boundary for bioelectromagnetic readout.
-- New formal structure: DASHI. This is a typed finite algebraic invariant,
-- not a derived Kaluza--Klein reduction of Einstein's field equations.
-- Maxwell electromagnetism remains 4D unless a geometrical realization
-- plus all required conditions is independently supplied.

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
import DASHI.Physics.Measurement.CausalBioelectromagneticExperimentExact as C

-- An abstract electromagnetic potential may have gauge-equivalent
-- representatives. Its field strength is insensitive to allowed gauges.
record GaugeFieldObservation {ℓ : Level}
  (Potential Field : Set ℓ) : Set ℓ where
  field
    gauge : Potential → Potential
    fieldStrength : Potential → Field
    gaugeInvariant : (a : Potential) →
      fieldStrength (gauge a) ≡ fieldStrength a
open GaugeFieldObservation public

-- A fifth fibre coordinate can label representatives without itself
-- contributing a new experimentally verified physical dimension.
record ExtraCoordinatePresentation {ℓ : Level}
  (Coordinate Potential : Set ℓ) : Set ℓ where
  field
    basePotential : Coordinate → Potential
    fibreShift : Coordinate → Coordinate
open ExtraCoordinatePresentation public

record CompatibleExtraCoordinate {ℓ : Level}
  {Coordinate Potential Field : Set ℓ}
  (x : ExtraCoordinatePresentation Coordinate Potential)
  (g : GaugeFieldObservation Potential Field) : Set ℓ where
  field
    shiftRepresentsGauge :
      (c : Coordinate) →
      basePotential x (fibreShift x c) ≡
      gauge g (basePotential x c)
open CompatibleExtraCoordinate public

extraCoordinateFieldInvariant :
  ∀ {ℓ} {Coordinate Potential Field : Set ℓ}
  (x : ExtraCoordinatePresentation Coordinate Potential)
  (g : GaugeFieldObservation Potential Field)
  (compat : CompatibleExtraCoordinate x g)
  (c : Coordinate) →
  fieldStrength g (basePotential x (fibreShift x c)) ≡
  fieldStrength g (basePotential x c)
extraCoordinateFieldInvariant x g compat c
  rewrite shiftRepresentsGauge compat c =
  gaugeInvariant g (basePotential x c)

-- The same observation can be built from multiple gauge representatives.
gaugeReadoutInvariant :
  ∀ {ℓ} {Potential Field Datum : Set ℓ}
  (g : GaugeFieldObservation Potential Field)
  (readout : C.MagneticReadout Field Datum)
  (a : Potential) →
  C.MagneticReadout.observation readout
    (fieldStrength g (gauge g a))
  ≡
  C.MagneticReadout.observation readout
    (fieldStrength g a)
gaugeReadoutInvariant g readout a =
  cong (C.MagneticReadout.observation readout) (gaugeInvariant g a)
