module DASHI.Biology.FiveHT2AVisualCortexBioelectricBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.KluverLogPolar5HT2ASourceAtlasExact as Sources
import DASHI.Biology.FiveHT2ASignalingDialecticExact as Signaling
import DASHI.Biology.FiveHT2AProtocolIndexedSignalTransportExact as Protocol
import DASHI.Biology.StateDependentMultiplexTransducer as Stateful
import DASHI.Biology.Cell.BioelectricNetwork as Bioelectric
import DASHI.Biology.Physical.SIBioelectricNetworkAdapterExact as SIAdapter
import DASHI.Biology.NeurochemicalBrainCarrierBridge as Brain

------------------------------------------------------------------------
-- CELL-TYPE-INDEXED VISUAL-CORTEX BRIDGE
--
-- Source side:
--   Barzan et al. 2024 isolate a 5-HT2A-pathway-like Gq manipulation in mouse
--   V1 pyramidal and PV neurons and report calcium, firing and visual-gain
--   effects.
--
--   White et al. 2026 report psychedelic-agonist-associated ~5-Hz activity in
--   visual and retrosplenial cortex.
--
-- DASHI side:
--   these observations are transported into existing cell/bioelectric/network
--   carriers without inventing membrane voltages, conductances or currents.
------------------------------------------------------------------------

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Sources.canonicalKluverLogPolar5HT2AAtlas

data VisualCortexCellClass : Set where
  pyramidalCell : VisualCortexCellClass
  pvInterneuron : VisualCortexCellClass
  putativeExcitatoryPopulation : VisualCortexCellClass
  putativeInhibitoryPopulation : VisualCortexCellClass

data CircuitReadoutKind : Set where
  calciumReadout : CircuitReadoutKind
  spontaneousFiringReadout : CircuitReadoutKind
  visuallyEvokedFiringReadout : CircuitReadoutKind
  visualGainReadout : CircuitReadoutKind
  orientationPreferenceReadout : CircuitReadoutKind
  oscillatoryReadout : CircuitReadoutKind

data DirectionalEffect : Set where
  increased : DirectionalEffect
  decreased : DirectionalEffect
  bidirectional : DirectionalEffect
  unchangedAtReportedResolution : DirectionalEffect
  sourceConditioned : DirectionalEffect

record VisualCortexSourceObservation : Set where
  constructor visualCortexSourceObservation
  field
    source : Source.AttributedSource
    manipulatedCellClass : VisualCortexCellClass
    observedCellClass : VisualCortexCellClass
    readout : CircuitReadoutKind
    effect : DirectionalEffect
    sourceReading : String

    mouseV1Specific : Bool
    humanPerceptualClaim : Bool
    humanPerceptualClaimIsFalse :
      humanPerceptualClaim ≡ false

open VisualCortexSourceObservation public

barzanPyramidalCalcium : VisualCortexSourceObservation
barzanPyramidalCalcium =
  visualCortexSourceObservation
    Sources.barzanEtAl2024
    pyramidalCell
    pyramidalCell
    calciumReadout
    increased
    "5-HT2A-pathway-targeted Gq activation produced a PLC-sensitive calcium response in the reported mouse V1 preparation."
    true
    false refl

barzanPyramidalExcitatoryFiring : VisualCortexSourceObservation
barzanPyramidalExcitatoryFiring =
  visualCortexSourceObservation
    Sources.barzanEtAl2024
    pyramidalCell
    putativeExcitatoryPopulation
    spontaneousFiringReadout
    increased
    "Pyramidal-pathway activation increased activity in a substantial excitatory-neuron subpopulation in the reported mouse V1 experiment."
    true
    false refl

barzanPyramidalInhibitoryFiring : VisualCortexSourceObservation
barzanPyramidalInhibitoryFiring =
  visualCortexSourceObservation
    Sources.barzanEtAl2024
    pyramidalCell
    putativeInhibitoryPopulation
    spontaneousFiringReadout
    increased
    "Pyramidal-pathway activation also increased inhibitory-population activity through a polysynaptic effect in the reported mouse V1 experiment."
    true
    false refl

barzanPVExcitatoryFiring : VisualCortexSourceObservation
barzanPVExcitatoryFiring =
  visualCortexSourceObservation
    Sources.barzanEtAl2024
    pvInterneuron
    putativeExcitatoryPopulation
    spontaneousFiringReadout
    decreased
    "PV-pathway activation suppressed the recorded excitatory population in the reported mouse V1 experiment."
    true
    false refl

barzanPVVisualGain : VisualCortexSourceObservation
barzanPVVisualGain =
  visualCortexSourceObservation
    Sources.barzanEtAl2024
    pvInterneuron
    putativeExcitatoryPopulation
    visualGainReadout
    decreased
    "PV-pathway activation reduced the gain of visually evoked excitatory responses relative to baseline in the reported mouse V1 experiment."
    true
    false refl

barzanOrientationPreference : VisualCortexSourceObservation
barzanOrientationPreference =
  visualCortexSourceObservation
    Sources.barzanEtAl2024
    pvInterneuron
    putativeExcitatoryPopulation
    orientationPreferenceReadout
    unchangedAtReportedResolution
    "The reported visual-gain effect did not require a change in preferred orientation."
    true
    false refl

whiteVisualOscillation : VisualCortexSourceObservation
whiteVisualOscillation =
  visualCortexSourceObservation
    Sources.whiteEtAl2026
    pyramidalCell
    putativeExcitatoryPopulation
    oscillatoryReadout
    increased
    "The source reports increased spontaneous and evoked approximately 5-Hz oscillatory activity after a psychedelic 5-HT2A agonist, including visual cortex."
    true
    false refl

canonicalVisualCortexSourceObservations :
  List VisualCortexSourceObservation
canonicalVisualCortexSourceObservations =
  barzanPyramidalCalcium
  ∷ barzanPyramidalExcitatoryFiring
  ∷ barzanPyramidalInhibitoryFiring
  ∷ barzanPVExcitatoryFiring
  ∷ barzanPVVisualGain
  ∷ barzanOrientationPreference
  ∷ whiteVisualOscillation
  ∷ []

------------------------------------------------------------------------
-- Existing bioelectric owners.
------------------------------------------------------------------------

abstractBioelectricNetwork : Bioelectric.BioelectricNetwork
abstractBioelectricNetwork = Stateful.canonicalBioelectricNetwork

siBioelectricNetwork : Bioelectric.BioelectricNetwork
siBioelectricNetwork = SIAdapter.canonicalSIBioelectricNetwork

brainCarrier : Brain.NeurochemicalBrainCarrierBridge
brainCarrier = Brain.canonicalNeurochemicalBrainCarrierBridge

------------------------------------------------------------------------
-- Exact structural reuse:
-- the pre-existing finite network already proves that changing only the
-- chemical/modulatory coordinate can change the successor network state.
------------------------------------------------------------------------

chemicalCoordinateCanChangeNetworkState :
  Bioelectric.BioelectricNetwork.update
    Stateful.canonicalBioelectricNetwork
    false false false false false
  ≡
  Bioelectric.BioelectricNetwork.update
    Stateful.canonicalBioelectricNetwork
    false true false false false
  →
  ⊥
chemicalCoordinateCanChangeNetworkState =
  Stateful.canonicalBioelectricChemicalModulation

------------------------------------------------------------------------
-- Measured source effects are not identified with SI quantities.
------------------------------------------------------------------------

record BioelectricMeasurementObligation : Set where
  constructor bioelectricMeasurementObligation
  field
    membraneVoltageProtocol : String
    ionicCurrentProtocol : String
    channelStateProtocol : String
    conductanceProtocol : String
    calciumProtocol : String
    cellTypeProtocol : String
    timeAlignmentProtocol : String

    voltageNumericallyRecoveredHere : Bool
    voltageNumericallyRecoveredHereIsFalse :
      voltageNumericallyRecoveredHere ≡ false

    currentNumericallyRecoveredHere : Bool
    currentNumericallyRecoveredHereIsFalse :
      currentNumericallyRecoveredHere ≡ false

    conductanceNumericallyRecoveredHere : Bool
    conductanceNumericallyRecoveredHereIsFalse :
      conductanceNumericallyRecoveredHere ≡ false

open BioelectricMeasurementObligation public

canonicalBioelectricMeasurementObligation :
  BioelectricMeasurementObligation
canonicalBioelectricMeasurementObligation =
  bioelectricMeasurementObligation
    "cell-type-resolved membrane-potential acquisition"
    "whole-cell or otherwise calibrated ionic-current acquisition"
    "channel-state or channel-specific pharmacological/biophysical assay"
    "conductance estimation under the same cell/protocol/time coordinate"
    "calcium imaging or calibrated intracellular calcium readout"
    "cell identity / layer / region receipt"
    "shared timestamp and perturbation alignment across receptor, calcium, current and firing readouts"
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Source observation -> bioelectric/network coordinate.
------------------------------------------------------------------------

data BioelectricCoordinate : Set where
  chemicalSignalCoordinate : BioelectricCoordinate
  calciumStateCoordinate : BioelectricCoordinate
  channelStateCoordinate : BioelectricCoordinate
  ionicCurrentCoordinate : BioelectricCoordinate
  voltageCoordinate : BioelectricCoordinate
  firingCoordinate : BioelectricCoordinate
  networkGainCoordinate : BioelectricCoordinate
  oscillatoryCoordinate : BioelectricCoordinate

record SourceToBioelectricCoordinate : Set where
  constructor sourceToBioelectricCoordinate
  field
    observation : VisualCortexSourceObservation
    coordinate : BioelectricCoordinate
    mappingStatus : Protocol.CrossProtocolNumericComparisonLicensed
      → ⊥
    reading : String

open SourceToBioelectricCoordinate public

-- The impossible function field is a deliberate firewall: this bridge carries
-- coordinate identity, not cross-protocol numeric calibration.

barzanCalciumCoordinate : SourceToBioelectricCoordinate
barzanCalciumCoordinate =
  sourceToBioelectricCoordinate
    barzanPyramidalCalcium
    calciumStateCoordinate
    Protocol.crossProtocolNumericComparisonRequiresCalibration
    "PLC-sensitive calcium response is admitted as a calcium-state coordinate; it is not converted into a membrane voltage/current without a same-protocol calibration."

------------------------------------------------------------------------
-- Cell/circuit cross-pollination bundle.
------------------------------------------------------------------------

record FiveHT2AVisualCortexBioelectricBridge : Set₁ where
  constructor fiveHT2AVisualCortexBioelectricBridge
  field
    signalingDialectic :
      Signaling.FiveHT2ASignalingDialectic

    protocolSignalTransport :
      Protocol.SignalToBrainCandidateWeld

    sourceObservations :
      List VisualCortexSourceObservation

    bioelectricOwner :
      Bioelectric.BioelectricNetwork

    siBioelectricOwner :
      Bioelectric.BioelectricNetwork

    brainOwner :
      Brain.NeurochemicalBrainCarrierBridge

    measurementObligations :
      BioelectricMeasurementObligation

    cellTypeSpecificityPreserved : Bool
    cellTypeSpecificityPreservedIsTrue :
      cellTypeSpecificityPreserved ≡ true

    directionalityPreserved : Bool
    directionalityPreservedIsTrue :
      directionalityPreserved ≡ true

    chemicalModulationCanAlterNetworkStateStructurally : Bool
    chemicalModulationCanAlterNetworkStateStructurallyIsTrue :
      chemicalModulationCanAlterNetworkStateStructurally ≡ true

    quantitativeVoltageCurrentTransferClosed : Bool
    quantitativeVoltageCurrentTransferClosedIsFalse :
      quantitativeVoltageCurrentTransferClosed ≡ false

    cellEffectDeterminesVisualForm : Bool
    cellEffectDeterminesVisualFormIsFalse :
      cellEffectDeterminesVisualForm ≡ false

    mouseV1ResultPromotedToHumanPsychedelicPercept : Bool
    mouseV1ResultPromotedToHumanPsychedelicPerceptIsFalse :
      mouseV1ResultPromotedToHumanPsychedelicPercept ≡ false

open FiveHT2AVisualCortexBioelectricBridge public

canonicalFiveHT2AVisualCortexBioelectricBridge :
  FiveHT2AVisualCortexBioelectricBridge
canonicalFiveHT2AVisualCortexBioelectricBridge =
  fiveHT2AVisualCortexBioelectricBridge
    Signaling.canonicalFiveHT2ASignalingDialectic
    Protocol.canonicalSignalToBrainCandidateWeld
    canonicalVisualCortexSourceObservations
    abstractBioelectricNetwork
    siBioelectricNetwork
    brainCarrier
    canonicalBioelectricMeasurementObligation
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Anti-collapse theorems.
------------------------------------------------------------------------

data CalciumSignalDeterminesVoltage : Set where
data FiringDirectionDeterminesChannelCurrent : Set where
data VisualGainChangeDeterminesKluverForm : Set where
data MouseV1CircuitEffectDeterminesHumanHallucination : Set where

calciumDoesNotDetermineVoltage :
  CalciumSignalDeterminesVoltage → ⊥
calciumDoesNotDetermineVoltage ()

firingDirectionDoesNotDetermineChannelCurrent :
  FiringDirectionDeterminesChannelCurrent → ⊥
firingDirectionDoesNotDetermineChannelCurrent ()

visualGainDoesNotDetermineKluverForm :
  VisualGainChangeDeterminesKluverForm → ⊥
visualGainDoesNotDetermineKluverForm ()

mouseV1DoesNotDetermineHumanHallucination :
  MouseV1CircuitEffectDeterminesHumanHallucination → ⊥
mouseV1DoesNotDetermineHumanHallucination ()

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

record VisualCortexBioelectricFrontier : Set where
  constructor visualCortexBioelectricFrontier
  field
    paid : String
    remainingCellGap : String
    remainingCircuitGap : String
    remainingPerceptGap : String
    nextHighestAlphaWeld : String

canonicalVisualCortexBioelectricFrontier :
  VisualCortexBioelectricFrontier
canonicalVisualCortexBioelectricFrontier =
  visualCortexBioelectricFrontier
    "cell-type-indexed V1 calcium/firing/gain/oscillation observations are source-bound and transported into existing bioelectric/network coordinate types"
    "same-protocol receptor/transducer -> calcium/channel/current/voltage quantitative transfer"
    "same-protocol cell effects -> spatially resolved V1 network mode / oscillatory field"
    "network mode -> retinotopic form-constant comparison under a frozen observation protocol"
    "reuse visual-pattern mode geometry to define a measured circuit-field observation, then compare its symmetry/log-polar projection against Kluever classes without inferring phenomenology from receptor activity alone"
