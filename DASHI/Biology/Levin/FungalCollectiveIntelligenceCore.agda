module DASHI.Biology.Levin.FungalCollectiveIntelligenceCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.FungalNetworkAgencyBoundary as Fungal
import DASHI.Biology.Levin.MycelialTransportTopology as Topology
import DASHI.Biology.Levin.FungalMemoryInterventionBoundary as Memory
import DASHI.Biology.Levin.FungalElectrochemicalHydraulicCoupling as Coupling
import DASHI.Biology.Levin.FungalPolycomputationAdapter as Poly
import DASHI.Biology.Levin.MycorrhizalTransferBenefitBoundary as Mycorrhiza
import DASHI.Biology.Levin.NicheConstructionProblemSpace as Niche

record FungalCollectiveIntelligenceCore : Set where
  field
    fungalAgencyBoundary : Fungal.FungalNetworkAgencyBoundary
    transportTopologyBoundary : Topology.MycelialTransportTopologyBoundary
    memoryBoundary : Memory.FungalMemoryInterventionBoundary
    carrierCouplingBoundary : Coupling.FungalElectrochemicalHydraulicBoundary
    polycomputationAdapter : Poly.FungalPolycomputationAdapter
    mycorrhizalBoundary : Mycorrhiza.MycorrhizalTransferBenefitBoundary
    nicheConstructionBoundary : Niche.NicheConstructionBoundary
    stametsMetaphorsRetainedAsHypothesisGenerators : Bool
    adamatzkyStylePhysicalComputationAdmissible : Bool
    simardStyleNetworkTransferRequiresBenefitGate : Bool
    sheldrakeStyleBoundaryQuestionsRemainScaleIndexed : Bool
    fungalIntelligenceNotSingleScalarProperty : Bool
    fungalConsciousnessNotPromoted : Bool
    interpretation : String

canonicalFungalCollectiveIntelligenceCore : FungalCollectiveIntelligenceCore
canonicalFungalCollectiveIntelligenceCore = record
  { fungalAgencyBoundary = Fungal.canonicalFungalNetworkAgencyBoundary
  ; transportTopologyBoundary = Topology.canonicalMycelialTransportTopologyBoundary
  ; memoryBoundary = Memory.canonicalFungalMemoryInterventionBoundary
  ; carrierCouplingBoundary = Coupling.canonicalFungalElectrochemicalHydraulicBoundary
  ; polycomputationAdapter = Poly.canonicalFungalPolycomputationAdapter
  ; mycorrhizalBoundary = Mycorrhiza.canonicalMycorrhizalTransferBenefitBoundary
  ; nicheConstructionBoundary = Niche.canonicalNicheConstructionBoundary
  ; stametsMetaphorsRetainedAsHypothesisGenerators = true
  ; adamatzkyStylePhysicalComputationAdmissible = true
  ; simardStyleNetworkTransferRequiresBenefitGate = true
  ; sheldrakeStyleBoundaryQuestionsRemainScaleIndexed = true
  ; fungalIntelligenceNotSingleScalarProperty = true
  ; fungalConsciousnessNotPromoted = true
  ; interpretation = "The fungal programme joins dynamic transport, durable history dependence, coupled carriers, observer-relative physical computation, mycorrhizal exchange and niche construction while preserving the distinction between adaptive distributed competence and consciousness"
  }
