module DASHI.Biology.Levin.CorticalFieldComputationCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.DynamicEffectiveTopology as Topology
import DASHI.Biology.Levin.MixedSelectivityFieldControl as Mixed
import DASHI.Biology.Levin.TravelingWaveComputationBoundary as Wave
import DASHI.Biology.Levin.OscillatoryMemoryStorageAdapter as Memory
import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as Chemistry
import DASHI.Biology.Levin.ExistingBiologyPhysicalStateAdapter as Existing
import DASHI.Biology.Levin.MillerTravelingWaveAccessProducerExact as Miller
import DASHI.Biology.Levin.WaveInterferenceRecruitmentExact as Interference
import DASHI.Biology.Levin.CrossFrequencyEffectiveTopologyExact as CrossFrequency
import DASHI.Biology.Levin.MixedSelectivityWaveAccessExact as MixedExact
import DASHI.Cognition.PNF.FastAccessControlFieldExact as Access

record CorticalFieldComputationCore : Set₁ where
  field
    fieldControlBoundary : Mixed.FieldControlBoundary
    travelingWaveBoundary : Wave.TravelingWaveBoundary
    memoryAdapter : Memory.OscillatoryMemoryAdapter
    chemistryAdapter : Chemistry.BioelectricChemistryWaveAdapter
    existingBiologyAdapter : Existing.ExistingBiologyPhysicalStateAdapter

    -- Exact producer layer added beneath the prior candidate boundaries.
    fastAccessProducer : Access.FastAccessControlField
    movingSupportActuallyChanges :
      Miller.recruitedAt Miller.firstTick Miller.leftSite
      ≡ Miller.recruitedAt Miller.secondTick Miller.leftSite → ⊥
    interferenceChangesRecruitment :
      Interference.nonzeroRecruit
        (Interference.combinedAmplitude Interference.one Interference.inPhase)
      ≡
      Interference.nonzeroRecruit
        (Interference.combinedAmplitude Interference.one Interference.antiPhase)
      → ⊥
    fixedAnatomyDynamicEdge :
      Topology.EffectiveEdge
        (CrossFrequency.betaState CrossFrequency.betaLow)
        Topology.associationNode Topology.planningNode
    sameEdgeClosedUnderOtherControl :
      Topology.EffectiveEdge
        (CrossFrequency.betaState CrossFrequency.betaHigh)
        Topology.associationNode Topology.planningNode → ⊥
    mixedSelectivityContextChangesParticipation :
      Miller.recruitedAt Miller.firstTick Miller.leftSite
      ≡ Miller.recruitedAt Miller.secondTick Miller.leftSite → ⊥

    measuredFieldEffectsAreNotEpiphenomenalByDefinition : Bool
    anesthesiaConvergenceDoesNotProveUniversalConsciousnessMechanism : Bool
    corticalBindingDoesNotSufficeForConsciousness : Bool
    waveOrganisationDoesNotEliminateSynapticComputation : Bool
    nonNeuralWavesDoNotBecomeCognitiveByShapeAlone : Bool
    candidateOnly : Bool
    interpretation : String

canonicalCorticalFieldComputationCore : CorticalFieldComputationCore
canonicalCorticalFieldComputationCore = record
  { fieldControlBoundary = Mixed.canonicalFieldControlBoundary
  ; travelingWaveBoundary = Wave.canonicalTravelingWaveBoundary
  ; memoryAdapter = Memory.canonicalOscillatoryMemoryAdapter
  ; chemistryAdapter = Chemistry.canonicalBioelectricChemistryWaveAdapter
  ; existingBiologyAdapter = Existing.canonicalExistingBiologyPhysicalStateAdapter
  ; fastAccessProducer = Miller.waveFastAccessField
  ; movingSupportActuallyChanges = Miller.movingSupportActuallyChanges
  ; interferenceChangesRecruitment = Interference.phaseDifferenceChangesRecruitment
  ; fixedAnatomyDynamicEdge = CrossFrequency.betaLowOpensExistingAnatomicalEdge
  ; sameEdgeClosedUnderOtherControl = CrossFrequency.betaHighClosesSameAnatomicalEdge
  ; mixedSelectivityContextChangesParticipation = MixedExact.sameStimulusContextChangesParticipation
  ; measuredFieldEffectsAreNotEpiphenomenalByDefinition = true
  ; anesthesiaConvergenceDoesNotProveUniversalConsciousnessMechanism = true
  ; corticalBindingDoesNotSufficeForConsciousness = true
  ; waveOrganisationDoesNotEliminateSynapticComputation = true
  ; nonNeuralWavesDoNotBecomeCognitiveByShapeAlone = true
  ; candidateOnly = true
  ; interpretation = "Mixed-selectivity, traveling-wave, memory and physical-chemistry surfaces now include exact fast-access, interference and fixed-anatomy/dynamic-topology witnesses without promoting oscillatory organisation to a complete theory of cognition or consciousness"
  }
