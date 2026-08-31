module DASHI.Governance.LevinAgenticMaterialRealisedTopologyCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.Levin.SubstrateIndependentAgency as Agency
import DASHI.Biology.Levin.SubstrateConstrainedComputation as Substrate
import DASHI.Biology.Levin.ObserverRelativePolycomputation as Poly
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy
import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.BiologicalComputationalConsciousnessBoundary as LevinConsciousness
import DASHI.Core.DeclaredRealisedInteractionTopologyExact as Runtime
import DASHI.Core.SharedStateCoalitionReachableEffectExact as Shared
import DASHI.Governance.ConsciousnessRealisedTopologyCrossPollinationExact as Consciousness

------------------------------------------------------------------------
-- LEVIN / AGENTIC-MATERIAL / REALISED-TOPOLOGY CROSS-POLLINATION
--
-- This owner does not define "agentic material" by label.  It separates:
--   material substrate
--   observer-relative computation reading
--   realised interaction topology
--   problem-space navigation / competency evidence
--   autonomy / maintained boundary evidence
--   consciousness and moral-status promotion.
------------------------------------------------------------------------

data MaterialOrganisation : Set where
  passiveLabel adaptiveMaterialOrganisation : MaterialOrganisation

data RealisedProtocol : Set where
  nominalOnly emergentSharedStateProtocol : RealisedProtocol

data GoalDirectedEvidence : Set where
  noGoalWitness perturbationRecoveryWitness : GoalDirectedEvidence

data ConsciousnessStatus : Set where
  consciousnessUnresolved : ConsciousnessStatus

data MoralStatus : Set where
  moralStatusUnresolved : MoralStatus

record AgenticMaterialCandidate : Set where
  constructor agentic-material-candidate
  field
    materialOrganisation : MaterialOrganisation
    realisedProtocol : RealisedProtocol
    goalEvidence : GoalDirectedEvidence
    consciousness : ConsciousnessStatus
    moralStatus : MoralStatus

open AgenticMaterialCandidate public

nominalMaterial : AgenticMaterialCandidate
nominalMaterial =
  agentic-material-candidate passiveLabel nominalOnly noGoalWitness
    consciousnessUnresolved moralStatusUnresolved

adaptiveCandidate : AgenticMaterialCandidate
adaptiveCandidate =
  agentic-material-candidate adaptiveMaterialOrganisation emergentSharedStateProtocol
    perturbationRecoveryWitness consciousnessUnresolved moralStatusUnresolved

consciousnessStillUnresolved :
  consciousness nominalMaterial ≡ consciousness adaptiveCandidate
consciousnessStillUnresolved = refl

moralStatusStillUnresolved :
  moralStatus nominalMaterial ≡ moralStatus adaptiveCandidate
moralStatusStillUnresolved = refl

------------------------------------------------------------------------
-- Imported canonical boundaries.
------------------------------------------------------------------------

agencyBoundary : Agency.SubstrateIndependentAgencyBoundary
agencyBoundary = Agency.canonicalSubstrateIndependentAgencyBoundary

substrateBoundary : Substrate.SubstrateConstrainedComputationBoundary
substrateBoundary = Substrate.canonicalSubstrateConstrainedComputationBoundary

observerBoundary : Poly.ObserverRelativePolycomputationBoundary
observerBoundary = Poly.canonicalObserverRelativePolycomputationBoundary

autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary

problemBoundary : Problem.ProblemSpaceAgencyBoundary
problemBoundary = Problem.canonicalProblemSpaceAgencyBoundary

levinConsciousnessBoundary : LevinConsciousness.BiologicalComputationalConsciousnessBoundary
levinConsciousnessBoundary =
  LevinConsciousness.canonicalBiologicalComputationalConsciousnessBoundary

runtimeBoundary : Runtime.DeclaredRealisedInteractionBoundary
runtimeBoundary = Runtime.canonicalDeclaredRealisedInteractionBoundary

sharedBoundary : Shared.SharedStateCoalitionBoundary
sharedBoundary = Shared.canonicalSharedStateCoalitionBoundary

consciousnessTopologyBoundary : Consciousness.ConsciousnessRealisedTopologyBoundary
consciousnessTopologyBoundary = Consciousness.canonicalConsciousnessRealisedTopologyBoundary

------------------------------------------------------------------------
-- Agency and consciousness are separately promoted.
------------------------------------------------------------------------

data AgenticMaterialLabelAutomaticallyProvesAgency : Set where

agenticLabelDoesNotProveAgency : AgenticMaterialLabelAutomaticallyProvesAgency → ⊥
agenticLabelDoesNotProveAgency ()

data GoalRecoveryAutomaticallyProvesConsciousness : Set where

goalRecoveryDoesNotProveConsciousness : GoalRecoveryAutomaticallyProvesConsciousness → ⊥
goalRecoveryDoesNotProveConsciousness ()

data EmergentProtocolAutomaticallyProvesConsciousness : Set where

emergentProtocolDoesNotProveConsciousness : EmergentProtocolAutomaticallyProvesConsciousness → ⊥
emergentProtocolDoesNotProveConsciousness ()

------------------------------------------------------------------------
-- Evidence expected for a serious agentic-material claim.
------------------------------------------------------------------------

record MaterialAgencyDiscriminator : Set where
  constructor material-agency-discriminator
  field
    physicalCarrierReference : String
    problemSpaceReference : String
    observableStateReference : String
    admissibleMoveReference : String
    targetRegionReference : String
    perturbationReference : String
    correctionOrRecoveryReference : String
    historyOrMemoryReference : String
    boundaryMaintenanceReference : String
    observerEncodingReference : String
    alternativeMechanismReference : String
    validationReference : String

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record LevinAgenticMaterialRealisedTopologyBoundary : Set where
  constructor levin-agentic-material-realised-topology-boundary
  field
    agenticMaterialLabelProvesAgency : Bool
    agenticMaterialLabelProvesAgencyIsFalse :
      agenticMaterialLabelProvesAgency ≡ false
    observerRelativeComputationMeansArbitraryReading : Bool
    observerRelativeComputationMeansArbitraryReadingIsFalse :
      observerRelativeComputationMeansArbitraryReading ≡ false
    declaredInterfaceFixesRealisedTopology : Bool
    declaredInterfaceFixesRealisedTopologyIsFalse :
      declaredInterfaceFixesRealisedTopology ≡ false
    substrateIndependentAgencyMeansSubstrateIrrelevant : Bool
    substrateIndependentAgencyMeansSubstrateIrrelevantIsFalse :
      substrateIndependentAgencyMeansSubstrateIrrelevant ≡ false
    goalDirectedRecoveryProvesConsciousness : Bool
    goalDirectedRecoveryProvesConsciousnessIsFalse :
      goalDirectedRecoveryProvesConsciousness ≡ false
    emergentCommunicationProvesConsciousness : Bool
    emergentCommunicationProvesConsciousnessIsFalse :
      emergentCommunicationProvesConsciousness ≡ false
    materialAgencyNeedsInterventionEvidence : Bool
    materialAgencyNeedsInterventionEvidenceIsTrue :
      materialAgencyNeedsInterventionEvidence ≡ true
    reading : String

canonicalLevinAgenticMaterialRealisedTopologyBoundary :
  LevinAgenticMaterialRealisedTopologyBoundary
canonicalLevinAgenticMaterialRealisedTopologyBoundary =
  levin-agentic-material-realised-topology-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    "Levin-style agency is treated as evidence-bearing navigation and correction in an explicit problem space, not as a material label. Observer-relative computation is constrained by empirical adequacy; realised topology can exceed the declared interface; substrate-independent comparison does not make substrate causally irrelevant; neither goal-directed recovery nor emergent communication automatically promotes to consciousness or moral status."
