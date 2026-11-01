module DASHI.Biology.NeurochemicalBrainCarrierBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.AnimalSenseObservationThreadDischarge as Thread
import DASHI.Biology.EvolvedSensoryTransport as Sensory
import DASHI.Biology.GenomeSensorimotorConnectomeBridge as Genome
import DASHI.Biology.NeurochemicalTransmissionBridge as Neuro
import DASHI.Promotion.NeurochemicalAuthorityBoundary as Boundary

------------------------------------------------------------------------
-- Candidate-only neurochemical-to-brain carrier bridge.
--
-- The bridge records protein target context, neurochemical transmission
-- context, and brain/circuit carrier context as a candidate-only surface.
-- It blocks brain-state recovery, mind-reading, behavior causation,
-- psychiatric diagnosis, and clinical/intervention authority.  The bridge
-- consumes the existing thread, evolved transport, genome/connectome,
-- neurochemical transmission, and authority-boundary records where that
-- consumption is mechanically available.

data Never : Set where

data ProteinTargetContext : Set where
  receptorTargetContext : ProteinTargetContext
  transporterTargetContext : ProteinTargetContext
  enzymeTargetContext : ProteinTargetContext
  channelTargetContext : ProteinTargetContext
  allostericSiteTargetContext : ProteinTargetContext

record BrainCarrierContext : Set where
  constructor brainCarrierContext
  field
    proteinTargetContext :
      ProteinTargetContext

    synapticContext :
      String

    volumeTransmission :
      String

    neuromodulatoryField :
      String

    cellTypeContext :
      String

    circuitRegionCandidate :
      String

    neuralEncoding :
      String

    plasticityModulation :
      String

    brainStateResidual :
      String

    behaviorQuotientResidual :
      String

open BrainCarrierContext public

data NeurochemicalBrainCarrierRoute : Set where
  candidateOnlyBridgeRoute : NeurochemicalBrainCarrierRoute
  brainStateRecoveryRoute : NeurochemicalBrainCarrierRoute
  mindReadingRoute : NeurochemicalBrainCarrierRoute
  behaviorCausationRoute : NeurochemicalBrainCarrierRoute
  psychiatricDiagnosisRoute : NeurochemicalBrainCarrierRoute
  clinicalAuthorityRoute : NeurochemicalBrainCarrierRoute
  interventionAuthorityRoute : NeurochemicalBrainCarrierRoute

AdmissibleNeurochemicalBrainCarrierRoute :
  NeurochemicalBrainCarrierRoute →
  Set
AdmissibleNeurochemicalBrainCarrierRoute candidateOnlyBridgeRoute =
  ⊤
AdmissibleNeurochemicalBrainCarrierRoute brainStateRecoveryRoute =
  Never
AdmissibleNeurochemicalBrainCarrierRoute mindReadingRoute =
  Never
AdmissibleNeurochemicalBrainCarrierRoute behaviorCausationRoute =
  Never
AdmissibleNeurochemicalBrainCarrierRoute psychiatricDiagnosisRoute =
  Never
AdmissibleNeurochemicalBrainCarrierRoute clinicalAuthorityRoute =
  Never
AdmissibleNeurochemicalBrainCarrierRoute interventionAuthorityRoute =
  Never

brainStateRecoveryRejected :
  AdmissibleNeurochemicalBrainCarrierRoute brainStateRecoveryRoute →
  Never
brainStateRecoveryRejected impossible =
  impossible

mindReadingRejected :
  AdmissibleNeurochemicalBrainCarrierRoute mindReadingRoute →
  Never
mindReadingRejected impossible =
  impossible

behaviorCausationRejected :
  AdmissibleNeurochemicalBrainCarrierRoute behaviorCausationRoute →
  Never
behaviorCausationRejected impossible =
  impossible

psychiatricDiagnosisRejected :
  AdmissibleNeurochemicalBrainCarrierRoute psychiatricDiagnosisRoute →
  Never
psychiatricDiagnosisRejected impossible =
  impossible

clinicalAuthorityRejected :
  AdmissibleNeurochemicalBrainCarrierRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRejected impossible =
  impossible

interventionAuthorityRejected :
  AdmissibleNeurochemicalBrainCarrierRoute interventionAuthorityRoute →
  Never
interventionAuthorityRejected impossible =
  impossible

record NeurochemicalBrainCarrierBridge : Set₁ where
  field
    threadDischarge :
      Thread.AnimalSenseObservationThreadDischarge

    threadDischargeIsCanonical :
      threadDischarge ≡
      Thread.canonicalAnimalSenseObservationThreadDischarge

    sensoryReceipt :
      Sensory.EvolvedSensoryTransportReceipt

    sensoryReceiptIsCanonical :
      sensoryReceipt ≡
      Thread.canonicalEvolvedSensoryTransportReceipt

    sensoryWitness :
      Sensory.EvolvedSensoryTransportPipelineWitness sensoryReceipt

    genomeBridge :
      Genome.GenomeSensorimotorConnectomeBridge

    genomeBridgeIsCanonical :
      genomeBridge ≡
      Genome.canonicalGenomeSensorimotorConnectomeBridge

    neurochemicalTransmissionBridge :
      Neuro.NeurochemicalTransmissionBridge

    neurochemicalTransmissionBridgeIsCanonical :
      neurochemicalTransmissionBridge ≡
      Neuro.canonicalNeurochemicalTransmissionBridge

    authorityBoundary :
      Boundary.NeurochemicalAuthorityBoundary

    authorityBoundaryIsCanonical :
      authorityBoundary ≡
      Boundary.canonicalNeurochemicalAuthorityBoundary

    authorityBoundaryClinicalFalse :
      Boundary.NeurochemicalAuthorityBoundary.clinicalValidityAccepted
        authorityBoundary
      ≡
      false

    authorityBoundaryInterventionFalse :
      Boundary.NeurochemicalAuthorityBoundary.interventionPromoted
        authorityBoundary
      ≡
      false

    brainCarrierContextValue :
      BrainCarrierContext

    route :
      NeurochemicalBrainCarrierRoute

    routeIsCandidateOnly :
      route ≡ candidateOnlyBridgeRoute

    routeAdmissible :
      AdmissibleNeurochemicalBrainCarrierRoute route

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    brainStateRecoveryBlocked :
      Bool

    brainStateRecoveryBlockedIsFalse :
      brainStateRecoveryBlocked ≡ false

    mindReadingBlocked :
      Bool

    mindReadingBlockedIsFalse :
      mindReadingBlocked ≡ false

    behaviorCausationBlocked :
      Bool

    behaviorCausationBlockedIsFalse :
      behaviorCausationBlocked ≡ false

    psychiatricDiagnosisBlocked :
      Bool

    psychiatricDiagnosisBlockedIsFalse :
      psychiatricDiagnosisBlocked ≡ false

    clinicalAuthorityBlocked :
      Bool

    clinicalAuthorityBlockedIsFalse :
      clinicalAuthorityBlocked ≡ false

    interventionAuthorityBlocked :
      Bool

    interventionAuthorityBlockedIsFalse :
      interventionAuthorityBlocked ≡ false

    bridgeReading :
      String

open NeurochemicalBrainCarrierBridge public

canonicalBrainCarrierContext :
  BrainCarrierContext
canonicalBrainCarrierContext =
  brainCarrierContext
    receptorTargetContext
    "synaptic transmission candidate"
    "volume transmission candidate"
    "neuromodulatory field candidate"
    "cell-type context candidate"
    "circuit region candidate"
    "neural encoding candidate"
    "plasticity modulation candidate"
    "brain-state residual candidate"
    "behavior quotient residual candidate"

canonicalNeurochemicalBrainCarrierBridge :
  NeurochemicalBrainCarrierBridge
canonicalNeurochemicalBrainCarrierBridge =
  record
    { threadDischarge =
        Thread.canonicalAnimalSenseObservationThreadDischarge
    ; threadDischargeIsCanonical =
        refl
    ; sensoryReceipt =
        Thread.canonicalEvolvedSensoryTransportReceipt
    ; sensoryReceiptIsCanonical =
        refl
    ; sensoryWitness =
        Thread.canonicalEvolvedSensoryTransportPipelineWitness
    ; genomeBridge =
        Genome.canonicalGenomeSensorimotorConnectomeBridge
    ; genomeBridgeIsCanonical =
        refl
    ; neurochemicalTransmissionBridge =
        Neuro.canonicalNeurochemicalTransmissionBridge
    ; neurochemicalTransmissionBridgeIsCanonical =
        refl
    ; authorityBoundary =
        Boundary.canonicalNeurochemicalAuthorityBoundary
    ; authorityBoundaryIsCanonical =
        refl
    ; authorityBoundaryClinicalFalse =
        Boundary.canonicalClinicalValidityProjectionIsFalse
    ; authorityBoundaryInterventionFalse =
        refl
    ; brainCarrierContextValue =
        canonicalBrainCarrierContext
    ; route =
        candidateOnlyBridgeRoute
    ; routeIsCandidateOnly =
        refl
    ; routeAdmissible =
        tt
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; brainStateRecoveryBlocked =
        Neuro.brainStateRecoveryAuthority
          Neuro.canonicalNeurochemicalTransmissionBridge
    ; brainStateRecoveryBlockedIsFalse =
        Neuro.brainStateRecoveryAuthorityIsFalse
          Neuro.canonicalNeurochemicalTransmissionBridge
    ; mindReadingBlocked =
        false
    ; mindReadingBlockedIsFalse =
        refl
    ; behaviorCausationBlocked =
        Neuro.behaviorCausationAuthority
          Neuro.canonicalNeurochemicalTransmissionBridge
    ; behaviorCausationBlockedIsFalse =
        Neuro.behaviorCausationAuthorityIsFalse
          Neuro.canonicalNeurochemicalTransmissionBridge
    ; psychiatricDiagnosisBlocked =
        Neuro.diagnosisAuthority
          Neuro.canonicalNeurochemicalTransmissionBridge
    ; psychiatricDiagnosisBlockedIsFalse =
        Neuro.diagnosisAuthorityIsFalse
          Neuro.canonicalNeurochemicalTransmissionBridge
    ; clinicalAuthorityBlocked =
        Neuro.clinicalAuthority
          Neuro.canonicalNeurochemicalTransmissionBridge
    ; clinicalAuthorityBlockedIsFalse =
        Neuro.clinicalAuthorityIsFalse
          Neuro.canonicalNeurochemicalTransmissionBridge
    ; interventionAuthorityBlocked =
        Boundary.NeurochemicalAuthorityBoundary.interventionPromoted
          Boundary.canonicalNeurochemicalAuthorityBoundary
    ; interventionAuthorityBlockedIsFalse =
        Boundary.NeurochemicalAuthorityBoundary.interventionPromotedIsFalse
          Boundary.canonicalNeurochemicalAuthorityBoundary
    ; bridgeReading =
        "Candidate-only bridge from neurochemical transmission and protein target context into brain/circuit carrier context: synaptic, volume, neuromodulatory, cell-type, circuit-region, neural-encoding, plasticity, brain-state residual, and behavior-quotient residual carriers are recorded while brain-state recovery, mind-reading, behavior causation, psychiatric diagnosis, and clinical/intervention authority remain blocked."
    }
