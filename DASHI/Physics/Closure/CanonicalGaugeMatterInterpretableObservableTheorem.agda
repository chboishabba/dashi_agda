module DASHI.Physics.Closure.CanonicalGaugeMatterInterpretableObservableTheorem where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.CanonicalGaugeMatterStrengtheningTheorem as CGMST

private
  canonicalStrengthening : CGMST.CanonicalGaugeMatterStrengtheningTheorem
  canonicalStrengthening = CGMST.canonicalGaugeMatterStrengtheningTheorem

  canonicalBundle : AGMB.AbstractGaugeMatterBundle
  canonicalBundle =
    CGMST.CanonicalGaugeMatterStrengtheningTheorem.canonicalBundle
      canonicalStrengthening

  canonicalRecovery : AGMB.GaugeMatterRecoveryTheorem canonicalBundle
  canonicalRecovery =
    CGMST.CanonicalGaugeMatterStrengtheningTheorem.gaugeMatterRecovery
      canonicalStrengthening

  canonicalContinuum : AGMB.ContinuumWitness canonicalBundle
  canonicalContinuum =
    CGMST.CanonicalGaugeMatterStrengtheningTheorem.strengthenedContinuum
      canonicalStrengthening

  canonicalTransport : AGMB.ObservableTransportWitness canonicalBundle
  canonicalTransport =
    AGMB.GaugeMatterRecoveryTheorem.transport canonicalRecovery

InterpretableCharge : Set
InterpretableCharge =
  AGMB.ContinuumWitness.LimitObservable canonicalContinuum

interpretableChargeFromCarrier :
  AGMB.Carrier canonicalBundle →
  InterpretableCharge
interpretableChargeFromCarrier x =
  AGMB.ContinuumWitness.limitObservable
    canonicalContinuum
    (AGMB.ContinuumWitness.scaleFromCarrier canonicalContinuum x)

observableProjectionInterpretable :
  AGMB.Observable canonicalBundle →
  InterpretableCharge
observableProjectionInterpretable =
  AGMB.ContinuumWitness.observableProjection canonicalContinuum

transportedObservableInterpretable :
  AGMB.ObservableTransportWitness.TargetCarrier canonicalTransport →
  InterpretableCharge
transportedObservableInterpretable x =
  observableProjectionInterpretable
    (AGMB.ObservableTransportWitness.observeTarget canonicalTransport x)

carrierObservableCompatible :
  ∀ x →
  interpretableChargeFromCarrier x
    ≡
  observableProjectionInterpretable
    (AGMB.observableOf canonicalBundle x)
carrierObservableCompatible x =
  trans
    (cong
      (AGMB.ContinuumWitness.limitObservable canonicalContinuum)
      (AGMB.ContinuumWitness.scale-lift-compatible canonicalContinuum x))
    (AGMB.ContinuumWitness.continuum-compatible canonicalContinuum x)

transportObservableCompatible :
  ∀ x →
  AGMB.admissible canonicalBundle x ≡ true →
  interpretableChargeFromCarrier x
    ≡
  transportedObservableInterpretable
    (AGMB.ObservableTransportWitness.transport canonicalTransport x)
transportObservableCompatible x ax =
  trans
    (carrierObservableCompatible x)
    (cong
      observableProjectionInterpretable
      (AGMB.ObservableTransportWitness.transport-sound
        canonicalTransport
        x
        ax))

------------------------------------------------------------------------
-- This theorem does not promote the canonical bundle to field recovery.
-- It only strengthens the current coarse conserved story by exhibiting a
-- richer transported observable invariant: the continuum-observable payload
-- induced from the existing theorem-bearing continuum witness.

record CanonicalGaugeMatterInterpretableObservableTheorem : Setω where
  field
    strengthening : CGMST.CanonicalGaugeMatterStrengtheningTheorem

    InterpretableChargeCarrier : Set

    carrier-observable-compatible :
      ∀ x →
      interpretableChargeFromCarrier x
        ≡
      observableProjectionInterpretable
        (AGMB.observableOf canonicalBundle x)

    transport-observable-compatible :
      ∀ x →
      AGMB.admissible canonicalBundle x ≡ true →
      interpretableChargeFromCarrier x
        ≡
      transportedObservableInterpretable
        (AGMB.ObservableTransportWitness.transport canonicalTransport x)

    interpretable-evolve :
      ∀ x →
      interpretableChargeFromCarrier x
        ≡
      interpretableChargeFromCarrier
        (AGMB.evolve canonicalBundle x)

    interpretable-coarse :
      ∀ x →
      interpretableChargeFromCarrier x
        ≡
      interpretableChargeFromCarrier
        (AGMB.coarse canonicalBundle x)

    interpretable-offset :
      ∀ x →
      interpretableChargeFromCarrier x
        ≡
      interpretableChargeFromCarrier
        (AGMB.offset canonicalBundle x)

canonicalGaugeMatterInterpretableObservableTheorem :
  CanonicalGaugeMatterInterpretableObservableTheorem
canonicalGaugeMatterInterpretableObservableTheorem =
  record
    { strengthening = canonicalStrengthening
    ; InterpretableChargeCarrier = InterpretableCharge
    ; carrier-observable-compatible = carrierObservableCompatible
    ; transport-observable-compatible = transportObservableCompatible
    ; interpretable-evolve =
        λ x →
          sym
            (cong
              (AGMB.ContinuumWitness.limitObservable canonicalContinuum)
              (AGMB.ContinuumWitness.scale-preserve-evolve
                canonicalContinuum
                x))
    ; interpretable-coarse =
        λ x →
          sym
            (cong
              (AGMB.ContinuumWitness.limitObservable canonicalContinuum)
              (AGMB.ContinuumWitness.scale-preserve-coarse
                canonicalContinuum
                x))
    ; interpretable-offset =
        λ x →
          sym
            (cong
              (AGMB.ContinuumWitness.limitObservable canonicalContinuum)
              (AGMB.ContinuumWitness.scale-preserve-offset
                canonicalContinuum
                x))
    }
