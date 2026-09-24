module DASHI.Biology.FiveHT2AProtocolIndexedSignalTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.SourceConditionedObservationExact as Observation
import DASHI.Biology.FiveHT2ASignalingDialecticExact as Signaling
import DASHI.Biology.StateDependentMultiplexTransducer as Stateful
import DASHI.Biology.NeurochemicalTransmissionBridge as Transmission
import DASHI.Biology.NeurochemicalBrainCarrierBridge as Brain

------------------------------------------------------------------------
-- PROTOCOL-INDEXED SIGNAL TRANSPORT
--
-- A signaling value is meaningless without its assay/protocol coordinate.
-- This module therefore transports only typed, source-conditioned signaling
-- observations.  It does not invent quantitative Gq/Gi/arrestin amplitudes.
------------------------------------------------------------------------

data ProtocolKind : Set where
  directTransducerBRET : ProtocolKind
  calciumFlux : ProtocolKind
  phospholipaseCIntervention : ProtocolKind
  cryoEMComplex : ProtocolKind
  inVivoBehavior : ProtocolKind
  humanSubjectiveBlockade : ProtocolKind
  humanNeuroimaging : ProtocolKind

record SignalingProtocol : Set where
  constructor signalingProtocol
  field
    protocolId : String
    protocolKind : ProtocolKind
    systemReference : String
    temperatureReference : String
    incubationReference : String
    concentrationReference : String
    readoutReference : String
    normalizationReference : String
    sourceReference : String

open SignalingProtocol public

record ProtocolIndexedTransducerObservation : Set where
  constructor protocolIndexedTransducerObservation
  field
    ligandReference : String
    receptorReference : String
    transducer : Signaling.FiveHT2ATransducer
    protocol : SignalingProtocol
    effectReference : String
    uncertaintyReference : String
    sourceClaim : Signaling.SourceConditionedSignalingClaim

    numericAmplitudeRecovered : Bool
    numericAmplitudeRecoveredIsFalse :
      numericAmplitudeRecovered ≡ false

open ProtocolIndexedTransducerObservation public

wallachGqProtocol : SignalingProtocol
wallachGqProtocol =
  signalingProtocol
    "Wallach-2023-Gq"
    directTransducerBRET
    "5-HT2A transducer assay system"
    "37 C"
    "source-indexed timepoints"
    "source-indexed concentration series"
    "Gq dissociation / efficacy"
    "5-HT-referenced efficacy"
    "10.1038/s41467-023-44016-1"

wallachArrestinProtocol : SignalingProtocol
wallachArrestinProtocol =
  signalingProtocol
    "Wallach-2023-beta-arrestin2"
    directTransducerBRET
    "5-HT2A transducer assay system"
    "37 C"
    "source-indexed timepoints"
    "source-indexed concentration series"
    "beta-arrestin2 recruitment / efficacy"
    "5-HT-referenced efficacy"
    "10.1038/s41467-023-44016-1"

xuGiStructureProtocol : SignalingProtocol
xuGiStructureProtocol =
  signalingProtocol
    "Xu-2026-Gi-structure"
    cryoEMComplex
    "5-HT2A-Gi complex"
    "cryo-EM preparation"
    "source protocol"
    "source ligand condition"
    "resolved receptor-transducer complex"
    "structural coordinate"
    "10.1038/s41586-025-10061-7"

wallachGqObservation : ProtocolIndexedTransducerObservation
wallachGqObservation =
  protocolIndexedTransducerObservation
    "source ligand series"
    "human 5-HT2A receptor"
    Signaling.gq11
    wallachGqProtocol
    "Gq efficacy tracked mouse HTR magnitude within the reported ligand/assay surface"
    "retain source statistics and assay limitations"
    Signaling.wallachGqHTR
    false refl

wallachArrestinObservation : ProtocolIndexedTransducerObservation
wallachArrestinObservation =
  protocolIndexedTransducerObservation
    "source ligand series"
    "human 5-HT2A receptor"
    Signaling.betaArrestin2
    wallachArrestinProtocol
    "beta-arrestin2 recruitment did not track HTR magnitude in the reported ligand/assay surface"
    "retain source statistics and assay limitations"
    Signaling.wallachArrestinHTR
    false refl

xuGiStructuralObservation : ProtocolIndexedTransducerObservation
xuGiStructuralObservation =
  protocolIndexedTransducerObservation
    "psychedelic ligand condition"
    "human 5-HT2A receptor"
    Signaling.gi
    xuGiStructureProtocol
    "5-HT2A-Gi complex structurally observed in the reported cryo-EM surface"
    "structural observation is not a quantitative in-vivo signaling amplitude"
    Signaling.xuGiStructure
    false refl

canonicalProtocolIndexedObservations :
  List ProtocolIndexedTransducerObservation
canonicalProtocolIndexedObservations =
  wallachGqObservation
  ∷ wallachArrestinObservation
  ∷ xuGiStructuralObservation
  ∷ []

------------------------------------------------------------------------
-- Protocol identity is proof-relevant.
------------------------------------------------------------------------

data SameProtocol : SignalingProtocol → SignalingProtocol → Set where
  sameProtocolRefl :
    (p : SignalingProtocol) →
    SameProtocol p p

data CrossProtocolNumericComparisonLicensed :
  ProtocolIndexedTransducerObservation →
  ProtocolIndexedTransducerObservation →
  Set where

crossProtocolNumericComparisonRequiresCalibration :
  CrossProtocolNumericComparisonLicensed
    wallachGqObservation
    xuGiStructuralObservation
  →
  ⊥
crossProtocolNumericComparisonRequiresCalibration ()

------------------------------------------------------------------------
-- Existing source-conditioned observation boundary is consumed rather than
-- reimplemented.
------------------------------------------------------------------------

sourceConditionedObservationBoundary :
  Observation.SourceConditionedObservationBoundary
sourceConditionedObservationBoundary =
  Observation.canonicalSourceConditionedObservationBoundary

------------------------------------------------------------------------
-- Signaling profile -> state-dependent neural modulation.
--
-- This is a finite structural theorem, not a calibrated biological neuron.
-- We reuse the existing Bool multiplex transducer:
--
--   same input
--   same prior state
--   different modulator
--       =>
--   different output / successor state.
--
-- The only biological reading licensed here is that a receptor-signaling
-- state may enter as one modulatory coordinate; no 5-HT2A-specific numeric
-- mapping to Bool is asserted.
------------------------------------------------------------------------

data SignalingModulatorClass : Set where
  baselineModulator : SignalingModulatorClass
  alteredModulator : SignalingModulatorClass

finiteModulatorCode : SignalingModulatorClass → Bool
finiteModulatorCode baselineModulator = false
finiteModulatorCode alteredModulator = true

sameInputBaselineOutput :
  Stateful.runOutput
    Stateful.canonicalBoolTransducer
    true
    false
    (finiteModulatorCode baselineModulator)
  ≡
  true
sameInputBaselineOutput = refl

sameInputAlteredOutput :
  Stateful.runOutput
    Stateful.canonicalBoolTransducer
    true
    false
    (finiteModulatorCode alteredModulator)
  ≡
  false
sameInputAlteredOutput = refl

signalingModulatorCanChangeOutputAtFixedInput :
  Stateful.runOutput
    Stateful.canonicalBoolTransducer
    true
    false
    (finiteModulatorCode baselineModulator)
  ≡
  Stateful.runOutput
    Stateful.canonicalBoolTransducer
    true
    false
    (finiteModulatorCode alteredModulator)
  →
  ⊥
signalingModulatorCanChangeOutputAtFixedInput ()

sameInputAlteredSuccessorState :
  Stateful.runState
    Stateful.canonicalBoolTransducer
    true
    false
    (finiteModulatorCode alteredModulator)
  ≡
  true
sameInputAlteredSuccessorState = refl

------------------------------------------------------------------------
-- Weld to existing neurochemical/brain candidate carriers.
------------------------------------------------------------------------

neurochemicalTransmission :
  Transmission.NeurochemicalTransmissionBridge
neurochemicalTransmission =
  Transmission.canonicalNeurochemicalTransmissionBridge

brainCarrier :
  Brain.NeurochemicalBrainCarrierBridge
brainCarrier =
  Brain.canonicalNeurochemicalBrainCarrierBridge

record SignalToBrainCandidateWeld : Set where
  constructor signalToBrainCandidateWeld
  field
    observations :
      List ProtocolIndexedTransducerObservation

    transmissionOwner :
      Transmission.NeurochemicalTransmissionBridge

    brainOwner :
      Brain.NeurochemicalBrainCarrierBridge

    stateDependentTransducer :
      Stateful.StatefulTransducer

    protocolIdentityPreserved : Bool
    protocolIdentityPreservedIsTrue :
      protocolIdentityPreserved ≡ true

    signalingCanModulateStateTransition : Bool
    signalingCanModulateStateTransitionIsTrue :
      signalingCanModulateStateTransition ≡ true

    quantitativeBiophysicalCalibrationPresent : Bool
    quantitativeBiophysicalCalibrationPresentIsFalse :
      quantitativeBiophysicalCalibrationPresent ≡ false

    receptorSignalDeterminesBrainState : Bool
    receptorSignalDeterminesBrainStateIsFalse :
      receptorSignalDeterminesBrainState ≡ false

open SignalToBrainCandidateWeld public

canonicalSignalToBrainCandidateWeld :
  SignalToBrainCandidateWeld
canonicalSignalToBrainCandidateWeld =
  signalToBrainCandidateWeld
    canonicalProtocolIndexedObservations
    neurochemicalTransmission
    brainCarrier
    Stateful.canonicalBoolTransducer
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Remaining experimental min-cut.
------------------------------------------------------------------------

record ProtocolIndexedSignalFrontier : Set where
  constructor protocolIndexedSignalFrontier
  field
    receptorOccupancyGap : String
    cellTypeGap : String
    circuitGap : String
    visualModeGap : String
    requiredJointProtocol : String

canonicalProtocolIndexedSignalFrontier : ProtocolIndexedSignalFrontier
canonicalProtocolIndexedSignalFrontier =
  protocolIndexedSignalFrontier
    "same-ligand concentration/timecourse -> receptor occupancy -> transducer amplitudes under one protocol"
    "cell-type-resolved downstream electrophysiology or signaling response"
    "region/network response aligned to the same perturbation and time axis"
    "visual-cortical mode / form-constant observation aligned to the same perturbation"
    "one provenance-preserving experiment bundle joining ligand exposure, receptor/transducer readout, cell/circuit response, and visual report or retinotopic observation"
