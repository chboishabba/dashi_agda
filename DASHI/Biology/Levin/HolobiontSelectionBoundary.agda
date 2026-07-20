module DASHI.Biology.Levin.HolobiontSelectionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.MultikingdomEmbodiedAgentCore as Multikingdom
import DASHI.Biology.Levin.ComponentCausalRoleBoundary as Causal
import DASHI.Biology.Levin.SymbiogenesisEvolutionaryIndividuality as Individuality

record HolobiontSelectionProtocol : Set where
  field
    hostLineageTracked : Bool
    microbialCommunityTracked : Bool
    transmissionModeMeasured : Bool
    betweenGenerationPersistenceMeasured : Bool
    hostFitnessMeasured : Bool
    microbialFitnessMeasured : Bool
    collectiveTraitHeritabilityMeasured : Bool
    environmentalReassemblyControlled : Bool
    hostFilteringMeasured : Bool
    competingSelectionModelsCompared : Bool

record HolobiontSelectionBoundary : Set where
  field
    multikingdomCore : Multikingdom.MultikingdomEmbodiedAgentCore
    causalRoleBoundary : Causal.ComponentCausalRoleBoundary
    individualityGate : Individuality.EvolutionaryIndividualityPromotionGate
    consortiumMembershipNotLevelOfSelection : Bool
    ecologicalIntegrationNotHeritability : Bool
    microbiomeTransmissionMustBeMeasured : Bool
    hostOrchestratedSpeciesSortingAdmissible : Bool
    holobiontSelectionAdmissibleWithCollectiveHeritability : Bool
    hostAndHolobiontModelsMayCompete : Bool
    hologenomeNotAssumed : Bool
    interpretation : String

canonicalHolobiontSelectionBoundary : HolobiontSelectionBoundary
canonicalHolobiontSelectionBoundary = record
  { multikingdomCore = Multikingdom.canonicalMultikingdomEmbodiedAgentCore
  ; causalRoleBoundary = Causal.canonicalComponentCausalRoleBoundary
  ; individualityGate = Individuality.canonicalEvolutionaryIndividualityPromotionGate
  ; consortiumMembershipNotLevelOfSelection = true
  ; ecologicalIntegrationNotHeritability = true
  ; microbiomeTransmissionMustBeMeasured = true
  ; hostOrchestratedSpeciesSortingAdmissible = true
  ; holobiontSelectionAdmissibleWithCollectiveHeritability = true
  ; hostAndHolobiontModelsMayCompete = true
  ; hologenomeNotAssumed = true
  ; interpretation = "Host plus microbiota may be modelled either as host-orchestrated ecological sorting or as a candidate holobiont level of selection; collective selection requires stable transmission and heritable collective variation rather than mere physiological integration"
  }
