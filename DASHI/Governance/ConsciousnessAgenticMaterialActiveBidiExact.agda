module DASHI.Governance.ConsciousnessAgenticMaterialActiveBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi
import DASHI.Core.ObservationInterventionTrustFibreExact as Observation
import DASHI.Core.DeclaredRealisedInteractionTopologyExact as Runtime
import DASHI.Core.HistoryConditionedChoiceExact as History
import DASHI.Governance.ConsciousnessPhysicalDiscriminatorSynthesisExact as Consciousness
import DASHI.Governance.LevinAgenticMaterialRealisedTopologyCrossPollinationExact as Levin
import DASHI.Planning.AgenticMaterialProcessPlanningCrossPollinationExact as Process

------------------------------------------------------------------------
-- CONSCIOUSNESS / AGENTIC-MATERIAL / PROCESS ACTIVE BIDI
--
-- The three domains share a search-and-verification grammar without sharing
-- their semantics.  A physical-consciousness theory, a material-competency
-- hypothesis, and a process-admissibility model may all need iterative
-- discrimination, but evidence for one lane is never proof for another.
------------------------------------------------------------------------

data DomainLane : Set where
  consciousnessTheoryLane
  agenticMaterialCompetencyLane
  industrialMaterialProcessLane
  : DomainLane

data DomainDisposition : Set where
  unresolvedRefine
  consumerAdequate
  authorisedOperationalAction
  : DomainDisposition

record DomainActiveBidiReceipt : Set where
  constructor domain-active-bidi-receipt
  field
    lane : DomainLane
    fineCarrierReference : String
    currentObserverReference : String
    hiddenResidualReference : String
    candidateHypothesisReference : String
    realisedTopologyReference : String
    discriminatorReference : String
    interventionReference : String
    interventionAuthorityReference : String
    observationProvenanceReference : String
    nuisanceControlReference : String
    fibreRefinementReference : String
    historyReference : String
    backwardConsumerReference : String
    dependencyReopeningReference : String
    nextExperimentReference : String
    disposition : DomainDisposition

------------------------------------------------------------------------
-- Canonical imported surfaces.
------------------------------------------------------------------------

activeBidiBoundary : Bidi.ActiveBidiDiscriminatorLoopBoundary
activeBidiBoundary = Bidi.canonicalActiveBidiDiscriminatorLoopBoundary

consciousnessBoundary : Consciousness.ConsciousnessPhysicalDiscriminatorBoundary
consciousnessBoundary = Consciousness.canonicalConsciousnessPhysicalDiscriminatorBoundary

levinBoundary : Levin.LevinAgenticMaterialRealisedTopologyBoundary
levinBoundary = Levin.canonicalLevinAgenticMaterialRealisedTopologyBoundary

processBoundary : Process.AgenticMaterialProcessPlanningBoundary
processBoundary = Process.canonicalAgenticMaterialProcessPlanningBoundary

observationBoundary : Observation.ObservationInterventionTrustBoundary
observationBoundary = Observation.canonicalObservationInterventionTrustBoundary

runtimeBoundary : Runtime.DeclaredRealisedInteractionBoundary
runtimeBoundary = Runtime.canonicalDeclaredRealisedInteractionBoundary

historyBoundary : History.HistoryConditionedChoiceBoundary
historyBoundary = History.canonicalHistoryConditionedChoiceBoundary

------------------------------------------------------------------------
-- Domain separation and BIDI transport boundary.
------------------------------------------------------------------------

record ConsciousnessAgenticMaterialActiveBidiBoundary : Set where
  constructor consciousness-agentic-material-active-bidi-boundary
  field
    commonBidiLoopMeansSameDomainSemantics : Bool
    commonBidiLoopMeansSameDomainSemanticsIsFalse :
      commonBidiLoopMeansSameDomainSemantics ≡ false
    materialCompetencyProvesConsciousness : Bool
    materialCompetencyProvesConsciousnessIsFalse :
      materialCompetencyProvesConsciousness ≡ false
    consciousnessDiscriminatorProvesMaterialAgency : Bool
    consciousnessDiscriminatorProvesMaterialAgencyIsFalse :
      consciousnessDiscriminatorProvesMaterialAgency ≡ false
    processAdmissibilityProvesAgency : Bool
    processAdmissibilityProvesAgencyIsFalse :
      processAdmissibilityProvesAgency ≡ false
    adaptiveProcessResponseProvesPhenomenology : Bool
    adaptiveProcessResponseProvesPhenomenologyIsFalse :
      adaptiveProcessResponseProvesPhenomenology ≡ false
    realisedTopologyMayForceObserverRefinement : Bool
    realisedTopologyMayForceObserverRefinementIsTrue :
      realisedTopologyMayForceObserverRefinement ≡ true
    historyMayChangeNextDiscriminator : Bool
    historyMayChangeNextDiscriminatorIsTrue :
      historyMayChangeNextDiscriminator ≡ true
    observationProvenanceRemainsIndependent : Bool
    observationProvenanceRemainsIndependentIsTrue :
      observationProvenanceRemainsIndependent ≡ true
    backwardConsumerRemainsExternallyGoverned : Bool
    backwardConsumerRemainsExternallyGovernedIsTrue :
      backwardConsumerRemainsExternallyGoverned ≡ true
    ontologyAndOperationalAuthorityRemainSeparate : Bool
    ontologyAndOperationalAuthorityRemainSeparateIsTrue :
      ontologyAndOperationalAuthorityRemainSeparate ≡ true
    reading : String

canonicalConsciousnessAgenticMaterialActiveBidiBoundary :
  ConsciousnessAgenticMaterialActiveBidiBoundary
canonicalConsciousnessAgenticMaterialActiveBidiBoundary =
  consciousness-agentic-material-active-bidi-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "Consciousness theory, Levin-style material competency and industrial process planning share an active BIDI grammar but not a common ontology. Forward hypotheses and interventions are separated from backward admission; realised topology and history can demand new measurements; observation provenance remains explicit; and neither agency, phenomenology nor operational authority is transported across domains without a dedicated receipt."
