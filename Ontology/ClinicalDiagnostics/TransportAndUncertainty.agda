module Ontology.ClinicalDiagnostics.TransportAndUncertainty where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAGMI

------------------------------------------------------------------------
-- Clinical diagnostic transport/constraint/uncertainty surface.
--
-- This module does not invent a parallel ontology.  It packages the
-- concrete gauge-matter witnesses already available in the canonical
-- abstract bundle into a diagnostic layer with three roles:
--
-- * transport of evidence
-- * conserved-observable constraints
-- * bounded uncertainty / frontier control
--
-- The witness fields are intentionally concrete and fail-closed: every
-- property below is discharged from the canonical bundle witnesses.

record TransportAndConstraintLayer : Setω where
  field
    bundle : AGMB.AbstractGaugeMatterBundle

    natural : AGMB.NaturalDynamicsWitness bundle
    conserved : AGMB.ConservedObservableWitness bundle
    continuum : AGMB.ContinuumWitness bundle
    signature : AGMB.SignatureLockWitness bundle
    transport : AGMB.ObservableTransportWitness bundle
    transportedProjectionDelta :
      AGMB.TransportedProjectionDeltaWitness bundle
    transportedProjectionDeltaAlt :
      AGMB.TransportedProjectionDeltaWitness bundle

    transport-of-evidence :
      ∀ x →
      AGMB.admissible bundle x ≡ true →
      AGMB.observableOf bundle x
        ≡
      AGMB.ObservableTransportWitness.observeTarget transport
        (AGMB.ObservableTransportWitness.transport transport x)

    conserved-observable-under-evolve :
      ∀ x →
      AGMB.admissible bundle x ≡ true →
      AGMB.ConservedObservableWitness.chargeOf conserved x
        ≡
      AGMB.ConservedObservableWitness.chargeOf conserved
        (AGMB.evolve bundle x)

    conserved-observable-under-coarse :
      ∀ x →
      AGMB.admissible bundle x ≡ true →
      AGMB.ConservedObservableWitness.chargeOf conserved x
        ≡
      AGMB.ConservedObservableWitness.chargeOf conserved
        (AGMB.coarse bundle x)

    signature-frontier-bounded :
      ∀ x →
      AGMB.admissible bundle x ≡ true →
      AGMB.SignatureLockWitness.signatureOf signature x
        ≡
      AGMB.SignatureLockWitness.lockedSignature signature

    signature-frontier-stable-evolve :
      ∀ x →
      AGMB.admissible bundle x ≡ true →
      AGMB.SignatureLockWitness.signatureOf signature x
        ≡
      AGMB.SignatureLockWitness.signatureOf signature
        (AGMB.evolve bundle x)

    signature-frontier-stable-coarse :
      ∀ x →
      AGMB.admissible bundle x ≡ true →
      AGMB.SignatureLockWitness.signatureOf signature x
        ≡
      AGMB.SignatureLockWitness.signatureOf signature
        (AGMB.coarse bundle x)

    continuum-frontier-compatible :
      ∀ x →
      AGMB.ContinuumWitness.limitObservable continuum
        (AGMB.ContinuumWitness.scaleToLimit continuum
          (AGMB.continuumLift bundle x))
        ≡
      AGMB.ContinuumWitness.observableProjection continuum
        (AGMB.observableOf bundle x)

open TransportAndConstraintLayer public

record DiagnosticUncertaintyFrontier : Setω where
  field
    frontierWitness :
      TransportAndConstraintLayer

    frontierCarrier : Set
    frontierOf : AGMB.Carrier (bundle frontierWitness) → frontierCarrier
    frontierBound : frontierCarrier

    frontierBoundedBySignature :
      ∀ x →
      AGMB.admissible (bundle frontierWitness) x ≡ true →
      frontierOf x
        ≡
      frontierBound

    frontierStableUnderEvolve :
      ∀ x →
      AGMB.admissible (bundle frontierWitness) x ≡ true →
      frontierOf x
        ≡
      frontierOf (AGMB.evolve (bundle frontierWitness) x)

    frontierStableUnderCoarse :
      ∀ x →
      AGMB.admissible (bundle frontierWitness) x ≡ true →
      frontierOf x
        ≡
      frontierOf (AGMB.coarse (bundle frontierWitness) x)

    frontierContinuumProjection :
      ∀ x →
      AGMB.ContinuumWitness.limitObservable
        (continuum frontierWitness)
        (AGMB.ContinuumWitness.scaleToLimit
          (continuum frontierWitness)
          (AGMB.continuumLift (bundle frontierWitness) x))
        ≡
      AGMB.ContinuumWitness.observableProjection
        (continuum frontierWitness)
        (AGMB.observableOf (bundle frontierWitness) x)

    frontierTransportEvidence :
      ∀ x →
      AGMB.admissible (bundle frontierWitness) x ≡ true →
      AGMB.observableOf (bundle frontierWitness) x
        ≡
      AGMB.ObservableTransportWitness.observeTarget
        (transport frontierWitness)
        (AGMB.ObservableTransportWitness.transport
          (transport frontierWitness) x)

canonicalTransportAndConstraintLayer : TransportAndConstraintLayer
canonicalTransportAndConstraintLayer = record
  { bundle = CAGMI.canonicalAbstractGaugeMatterBundle
  ; natural = CAGMI.canonicalNaturalDynamicsWitness
  ; conserved = CAGMI.canonicalConservedObservableWitness
  ; continuum = CAGMI.canonicalContinuumWitness
  ; signature = CAGMI.canonicalSignatureLockWitness
  ; transport = CAGMI.canonicalObservableTransportWitness
  ; transportedProjectionDelta =
      CAGMI.canonicalTransportedProjectionDeltaWitness
  ; transportedProjectionDeltaAlt =
      CAGMI.canonicalTransportedProjectionDeltaWitnessAlt
  ; transport-of-evidence =
      AGMB.ObservableTransportWitness.transport-sound
        CAGMI.canonicalObservableTransportWitness
  ; conserved-observable-under-evolve =
      AGMB.ConservedObservableWitness.charge-evolve
        CAGMI.canonicalConservedObservableWitness
  ; conserved-observable-under-coarse =
      AGMB.ConservedObservableWitness.charge-coarse
        CAGMI.canonicalConservedObservableWitness
  ; signature-frontier-bounded =
      AGMB.SignatureLockWitness.signature-locked
        CAGMI.canonicalSignatureLockWitness
  ; signature-frontier-stable-evolve =
      AGMB.SignatureLockWitness.signature-evolve
        CAGMI.canonicalSignatureLockWitness
  ; signature-frontier-stable-coarse =
      AGMB.SignatureLockWitness.signature-coarse
        CAGMI.canonicalSignatureLockWitness
  ; continuum-frontier-compatible =
      AGMB.ContinuumWitness.continuum-compatible
        CAGMI.canonicalContinuumWitness
  }

canonicalDiagnosticUncertaintyFrontier : DiagnosticUncertaintyFrontier
canonicalDiagnosticUncertaintyFrontier = record
  { frontierWitness = canonicalTransportAndConstraintLayer
  ; frontierCarrier =
      AGMB.SignatureLockWitness.SignatureClass
        CAGMI.canonicalSignatureLockWitness
  ; frontierOf =
      AGMB.SignatureLockWitness.signatureOf
        CAGMI.canonicalSignatureLockWitness
  ; frontierBound =
      AGMB.SignatureLockWitness.lockedSignature
        CAGMI.canonicalSignatureLockWitness
  ; frontierBoundedBySignature =
      AGMB.SignatureLockWitness.signature-locked
        CAGMI.canonicalSignatureLockWitness
  ; frontierStableUnderEvolve =
      AGMB.SignatureLockWitness.signature-evolve
        CAGMI.canonicalSignatureLockWitness
  ; frontierStableUnderCoarse =
      AGMB.SignatureLockWitness.signature-coarse
        CAGMI.canonicalSignatureLockWitness
  ; frontierContinuumProjection =
      AGMB.ContinuumWitness.continuum-compatible
        CAGMI.canonicalContinuumWitness
  ; frontierTransportEvidence =
      AGMB.ObservableTransportWitness.transport-sound
        CAGMI.canonicalObservableTransportWitness
  }
