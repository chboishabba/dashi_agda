module DASHI.Physics.Measurement.BioEMKaluzaDonorAdapterExact where

-- Concrete reuse of PR #1239's KK additive-group local-connection proof.
-- Donor file carried verbatim onto this branch; no physical 5D reduction.
-- The only statement here is observation invariance under that donor gauge law.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Electromagnetism.KaluzaKleinGaugeShiftExact as KK
import DASHI.Physics.Measurement.BioEMKaluzaObservationTransportExact as Transport
import DASHI.Physics.Measurement.CausalBioelectromagneticExperimentExact as Bio

module Concrete (Form : Set) (group : KK.AdditiveGroup Form) where
  module Donor = KK.Gauge Form group

  concreteConnection : Transport.LocalKKConnection Form
  concreteConnection = record
    { connection = Donor.kkConnection
    ; shiftedVertical = Donor.gaugeVertical
    ; shiftedPotential = Donor.gaugePotential
    ; horizontalInvariant = Donor.gaugeInvariant
    }

  concreteMagneticObservationInvariant :
    {Field Datum : Set}
    (field : Form → Field)
    (sensor : Bio.MagneticReadout Field Datum)
    (vertical potential displacement : Form) →
    Bio.MagneticReadout.observation sensor
      (field (Donor.kkConnection
        (Donor.gaugeVertical vertical displacement)
        (Donor.gaugePotential potential displacement)))
    ≡
    Bio.MagneticReadout.observation sensor
      (field (Donor.kkConnection vertical potential))
  concreteMagneticObservationInvariant field sensor vertical potential displacement =
    Donor.gaugeInvariantUnderObservable
      (λ x → Bio.MagneticReadout.observation sensor (field x))
      vertical potential displacement

  concreteFrequencyObservationInvariant :
    {Field Frequency : Set}
    (field : Form → Field)
    (sensor : Transport.FrequencySensor Field Frequency)
    (vertical potential displacement : Form) →
    Transport.FrequencySensor.frequency sensor
      (field (Donor.kkConnection
        (Donor.gaugeVertical vertical displacement)
        (Donor.gaugePotential potential displacement)))
    ≡
    Transport.FrequencySensor.frequency sensor
      (field (Donor.kkConnection vertical potential))
  concreteFrequencyObservationInvariant field sensor vertical potential displacement =
    Donor.gaugeInvariantUnderObservable
      (λ x → Transport.FrequencySensor.frequency sensor (field x))
      vertical potential displacement
