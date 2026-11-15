module DASHI.Physics.Measurement.BioEMKaluzaObservationTransportExact where

-- Downstream physical observation transport for the KK local connection.
-- Donor PR #1239: KaluzaKleinGaugeShiftExact. No duplicate group proof.
-- This file is an independent consumer contract until sibling branches merge.
-- Provenance: classical Kaluza/Klein gauge geometry; formal consumer DASHI.

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
import DASHI.Physics.Measurement.CausalBioelectromagneticExperimentExact as Bio

record LocalKKConnection {ℓ : Level} (Form : Set ℓ) : Set ℓ where
  field
    connection : Form → Form → Form
    shiftedVertical : Form → Form → Form
    shiftedPotential : Form → Form → Form
    horizontalInvariant :
      (v a d : Form) →
      connection (shiftedVertical v d) (shiftedPotential a d)
        ≡ connection v a
open LocalKKConnection public

-- The KK donor's theta-invariant connection can be consumed by any
-- field-strength or magnetic readout function. Does not assert that
-- its argument is a physical solution of Einstein/Maxwell equations.
localKKReadoutInvariant :
  ∀ {ℓ} {Form Field Datum : Set ℓ}
  (kk : LocalKKConnection Form)
  (field : Form → Field)
  (sensor : Bio.MagneticReadout Field Datum)
  (v a displacement : Form) →
  Bio.MagneticReadout.observation sensor
    (field (connection kk (shiftedVertical kk v displacement)
                          (shiftedPotential kk a displacement)))
  ≡
  Bio.MagneticReadout.observation sensor
    (field (connection kk v a))
localKKReadoutInvariant kk field sensor v a displacement =
  cong (λ theta → Bio.MagneticReadout.observation sensor (field theta))
       (horizontalInvariant kk v a displacement)

-- Stronger bridge from magnetic observable to a symbolic spin-frequency
-- must additionally exhibit a calibrated map Field -> Frequency.
record FrequencySensor {ℓ : Level}
  (Field Frequency : Set ℓ) : Set ℓ where
  field
    frequency : Field → Frequency
open FrequencySensor public

localKKFrequencyInvariant :
  ∀ {ℓ} {Form Field Frequency : Set ℓ}
  (kk : LocalKKConnection Form)
  (field : Form → Field)
  (sensor : FrequencySensor Field Frequency)
  (v a displacement : Form) →
  frequency sensor
    (field (connection kk (shiftedVertical kk v displacement)
                          (shiftedPotential kk a displacement)))
  ≡
  frequency sensor (field (connection kk v a))
localKKFrequencyInvariant kk field sensor v a displacement =
  cong (λ theta → frequency sensor (field theta))
       (horizontalInvariant kk v a displacement)
