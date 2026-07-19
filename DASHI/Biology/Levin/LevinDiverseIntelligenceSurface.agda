module DASHI.Biology.Levin.LevinDiverseIntelligenceSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.LevinBioelectricAgencyCore as Bioelectric
import DASHI.Biology.Levin.CorticalFieldComputationCore as Cortical
import DASHI.Biology.Levin.BioelectricCyberneticAgingCore as Aging
import DASHI.Biology.Levin.EvolutionaryLearningGeometryCore as Evolution
import DASHI.Biology.Levin.CompressionIntelligenceBoundaryCore as Compression
import DASHI.Biology.Levin.MultikingdomEmbodiedAgentCore as Multikingdom
import DASHI.Biology.Levin.FungalCollectiveIntelligenceCore as Fungal
import DASHI.Biology.Levin.CrossKingdomMinimalCognition as CrossKingdom
import DASHI.Biology.Levin.SymbiogenesisEvolutionaryIndividuality as Individuality
import DASHI.Biology.Levin.HolobiontSelectionBoundary as Holobiont
import DASHI.Biology.Levin.HostManipulationCausalSpectrum as Manipulation
import DASHI.Biology.Levin.BiologicalComputationalConsciousnessBoundary as Consciousness

record LevinDiverseIntelligenceSurface : Set where
  field
    bioelectricAgencyCore : Bioelectric.LevinBioelectricAgencyCore
    corticalFieldCore : Cortical.CorticalFieldComputationCore
    agingCore : Aging.BioelectricCyberneticAgingCore
    evolutionaryGeometryCore : Evolution.EvolutionaryLearningGeometryCore
    compressionBoundary : Compression.CompressionIntelligenceBoundary
    multikingdomCore : Multikingdom.MultikingdomEmbodiedAgentCore
    fungalCore : Fungal.FungalCollectiveIntelligenceCore
    crossKingdomBoundary : CrossKingdom.CrossKingdomMinimalCognitionBoundary
    individualityGate : Individuality.EvolutionaryIndividualityPromotionGate
    holobiontBoundary : Holobiont.HolobiontSelectionBoundary
    manipulationSpectrum : Manipulation.HostManipulationCausalSpectrum
    consciousnessBoundary : Consciousness.BiologicalComputationalConsciousnessBoundary
    scaleMustBeExplicit : Bool
    problemSpaceMustBeExplicit : Bool
    carrierMustBeExplicit : Bool
    interventionMustBeExplicit : Bool
    observerReadingMustBeExplicit : Bool
    componentInfluenceNotExclusiveAuthorship : Bool
    competenceNotConsciousness : Bool
    clinicalAndEcologicalAuthorityRemainSeparate : Bool
    interpretation : String

canonicalLevinDiverseIntelligenceSurface : LevinDiverseIntelligenceSurface
canonicalLevinDiverseIntelligenceSurface = record
  { bioelectricAgencyCore = Bioelectric.canonicalLevinBioelectricAgencyCore
  ; corticalFieldCore = Cortical.canonicalCorticalFieldComputationCore
  ; agingCore = Aging.canonicalBioelectricCyberneticAgingCore
  ; evolutionaryGeometryCore = Evolution.canonicalEvolutionaryLearningGeometryCore
  ; compressionBoundary = Compression.canonicalCompressionIntelligenceBoundary
  ; multikingdomCore = Multikingdom.canonicalMultikingdomEmbodiedAgentCore
  ; fungalCore = Fungal.canonicalFungalCollectiveIntelligenceCore
  ; crossKingdomBoundary = CrossKingdom.canonicalCrossKingdomMinimalCognitionBoundary
  ; individualityGate = Individuality.canonicalEvolutionaryIndividualityPromotionGate
  ; holobiontBoundary = Holobiont.canonicalHolobiontSelectionBoundary
  ; manipulationSpectrum = Manipulation.canonicalHostManipulationCausalSpectrum
  ; consciousnessBoundary = Consciousness.canonicalBiologicalComputationalConsciousnessBoundary
  ; scaleMustBeExplicit = true
  ; problemSpaceMustBeExplicit = true
  ; carrierMustBeExplicit = true
  ; interventionMustBeExplicit = true
  ; observerReadingMustBeExplicit = true
  ; componentInfluenceNotExclusiveAuthorship = true
  ; competenceNotConsciousness = true
  ; clinicalAndEcologicalAuthorityRemainSeparate = true
  ; interpretation = "Unified candidate surface for bioelectric, neural-field, evolutionary, informational, multikingdom, fungal, collective and manipulation-indexed intelligence claims; every promotion remains typed by scale, problem space, physical carrier, intervention and observer-relative reading"
  }
