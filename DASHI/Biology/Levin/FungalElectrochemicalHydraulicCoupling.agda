module DASHI.Biology.Levin.FungalElectrochemicalHydraulicCoupling where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as Electrochem
import DASHI.Biology.Levin.TravelingWaveComputationBoundary as Wave
import DASHI.Biology.Levin.MycelialTransportTopology as Topology

record FungalCarrierObservation : Set where
  field
    voltageMeasured : Bool
    ionOrMetaboliteStateMeasured : Bool
    pressureOrFlowMeasured : Bool
    growthFrontMeasured : Bool
    temporalRegistrationSpecified : Bool
    spatialRegistrationSpecified : Bool
    carrierPerturbationSpecified : Bool
    downstreamResponseMeasured : Bool

record FungalElectrochemicalHydraulicBoundary : Set where
  field
    electrochemicalAdapter : Electrochem.BioelectricChemistryWaveAdapter
    travelingWaveBoundary : Wave.TravelingWaveBoundary
    topologyBoundary : Topology.MycelialTransportTopologyBoundary
    electricalChemicalHydraulicSeparated : Bool
    couplingAmongCarriersAdmissible : Bool
    voltageEventNotMessageByDefinition : Bool
    spikeShapeNotSymbolByDefinition : Bool
    propagationNotComputationWithoutEncodingAndDecoding : Bool
    causalCarrierClaimRequiresSelectivePerturbation : Bool
    interpretation : String

canonicalFungalElectrochemicalHydraulicBoundary : FungalElectrochemicalHydraulicBoundary
canonicalFungalElectrochemicalHydraulicBoundary = record
  { electrochemicalAdapter = Electrochem.canonicalBioelectricChemistryWaveAdapter
  ; travelingWaveBoundary = Wave.canonicalTravelingWaveBoundary
  ; topologyBoundary = Topology.canonicalMycelialTransportTopologyBoundary
  ; electricalChemicalHydraulicSeparated = true
  ; couplingAmongCarriersAdmissible = true
  ; voltageEventNotMessageByDefinition = true
  ; spikeShapeNotSymbolByDefinition = true
  ; propagationNotComputationWithoutEncodingAndDecoding = true
  ; causalCarrierClaimRequiresSelectivePerturbation = true
  ; interpretation = "Fungal voltage, ionic or metabolic state, pressure-driven flow and growth are distinct but coupled carriers; a recorded spike becomes a computational signal only after reproducible encoding, propagation, decoding and carrier-selective intervention"
  }
