module Ontology.ClinicalDiagnostics.BridgeFromExistingReceipts where

open import Agda.Primitive using (Setω)

open import Ontology.BrainDNA.BrainCodecAdmissibilityBridge using
  (BrainCodecAdmissibilityBridgeSurface;
   brainCodecAdmissibilityBridgeSurface)
open import Ontology.BrainDNA.BrainSummaryStructuralConsumer using
  (BrainSummaryStructuralConsumerSurface;
   brainSummaryStructuralConsumerSurface)
open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB using
  (AbstractGaugeMatterBundle;
   NaturalDynamicsWitness;
   ObservableTransportWitness;
   TransportedProjectionDeltaWitness;
   GaugeMatterRecoveryTheorem)
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance using
  (canonicalAbstractGaugeMatterBundle;
   canonicalNaturalDynamicsWitness;
   canonicalObservableTransportWitness;
   canonicalTransportedProjectionDeltaWitness;
   canonicalGaugeMatterRecoveryTheorem)

------------------------------------------------------------------------
-- Bridge surface from the existing BrainDNA receipts into the clinical
-- diagnostic formalism.
--
-- This file does not introduce a parallel hierarchy. It exposes the
-- already-inhabited evidence, test, transport, and admissibility surfaces
-- and threads the canonical abstract gauge-matter instance through them.

record ClinicalDiagnosticsBridgeSurface : Setω where
  field
    evidence : BrainCodecAdmissibilityBridgeSurface
    tests : BrainSummaryStructuralConsumerSurface
    bundle : AbstractGaugeMatterBundle
    admissibility : NaturalDynamicsWitness bundle
    transport : ObservableTransportWitness bundle
    transportDelta : TransportedProjectionDeltaWitness bundle
    recovery : GaugeMatterRecoveryTheorem bundle

canonicalClinicalDiagnosticsBridgeSurface :
  ClinicalDiagnosticsBridgeSurface
canonicalClinicalDiagnosticsBridgeSurface = record
  { evidence = brainCodecAdmissibilityBridgeSurface
  ; tests = brainSummaryStructuralConsumerSurface
  ; bundle = canonicalAbstractGaugeMatterBundle
  ; admissibility = canonicalNaturalDynamicsWitness
  ; transport = canonicalObservableTransportWitness
  ; transportDelta = canonicalTransportedProjectionDeltaWitness
  ; recovery = canonicalGaugeMatterRecoveryTheorem
  }

clinicalEvidenceBridge :
  BrainCodecAdmissibilityBridgeSurface
clinicalEvidenceBridge =
  ClinicalDiagnosticsBridgeSurface.evidence
    canonicalClinicalDiagnosticsBridgeSurface

clinicalTestsBridge :
  BrainSummaryStructuralConsumerSurface
clinicalTestsBridge =
  ClinicalDiagnosticsBridgeSurface.tests
    canonicalClinicalDiagnosticsBridgeSurface

clinicalCanonicalBundle : AbstractGaugeMatterBundle
clinicalCanonicalBundle =
  ClinicalDiagnosticsBridgeSurface.bundle
    canonicalClinicalDiagnosticsBridgeSurface

clinicalAdmissibilityWitness :
  NaturalDynamicsWitness clinicalCanonicalBundle
clinicalAdmissibilityWitness =
  ClinicalDiagnosticsBridgeSurface.admissibility
    canonicalClinicalDiagnosticsBridgeSurface

clinicalTransportWitness :
  ObservableTransportWitness clinicalCanonicalBundle
clinicalTransportWitness =
  ClinicalDiagnosticsBridgeSurface.transport
    canonicalClinicalDiagnosticsBridgeSurface

clinicalTransportDeltaWitness :
  TransportedProjectionDeltaWitness clinicalCanonicalBundle
clinicalTransportDeltaWitness =
  ClinicalDiagnosticsBridgeSurface.transportDelta
    canonicalClinicalDiagnosticsBridgeSurface

clinicalRecoveryWitness :
  GaugeMatterRecoveryTheorem clinicalCanonicalBundle
clinicalRecoveryWitness =
  ClinicalDiagnosticsBridgeSurface.recovery
    canonicalClinicalDiagnosticsBridgeSurface
