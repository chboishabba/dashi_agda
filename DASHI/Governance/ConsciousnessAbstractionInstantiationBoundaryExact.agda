module DASHI.Governance.ConsciousnessAbstractionInstantiationBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- CONSCIOUSNESS: ABSTRACTION / SIMULATION / PHYSICAL INSTANTIATION BOUNDARY
--
-- This is a generic DASHI owner.  It does not prove that current AI is or is
-- not conscious.  It separates behavioural/computational equivalence from the
-- physical constitution that a substrate-sensitive theory may require.
------------------------------------------------------------------------

data BehaviourSurface : Set where
  sameConsciousLikeBehaviour : BehaviourSurface

data AbstractCausalTopology : Set where
  sameAbstractTopology : AbstractCausalTopology

data PhysicalConstitution : Set where
  constitutionAlpha constitutionBeta : PhysicalConstitution

data InstantiationStatus : Set where
  instantiationUnresolved instantiationSupported instantiationRejected : InstantiationStatus

data SimulationStatus : Set where
  simulationPresent simulationAbsent : SimulationStatus

record ConsciousnessCandidate : Set where
  constructor consciousness-candidate
  field
    behaviour : BehaviourSurface
    abstractTopology : AbstractCausalTopology
    physicalConstitution : PhysicalConstitution
    simulationStatus : SimulationStatus
    instantiationStatus : InstantiationStatus

open ConsciousnessCandidate public

candidateAlpha : ConsciousnessCandidate
candidateAlpha =
  consciousness-candidate
    sameConsciousLikeBehaviour
    sameAbstractTopology
    constitutionAlpha
    simulationPresent
    instantiationUnresolved

candidateBeta : ConsciousnessCandidate
candidateBeta =
  consciousness-candidate
    sameConsciousLikeBehaviour
    sameAbstractTopology
    constitutionBeta
    simulationPresent
    instantiationRejected

sameBehaviour : behaviour candidateAlpha ≡ behaviour candidateBeta
sameBehaviour = refl

sameAbstractStructure : abstractTopology candidateAlpha ≡ abstractTopology candidateBeta
sameAbstractStructure = refl

physicalConstitutionDiffers :
  physicalConstitution candidateAlpha ≡ physicalConstitution candidateBeta → ⊥
physicalConstitutionDiffers ()

instantiationStatusDiffers :
  instantiationStatus candidateAlpha ≡ instantiationStatus candidateBeta → ⊥
instantiationStatusDiffers ()

------------------------------------------------------------------------
-- Promotion barriers.
------------------------------------------------------------------------

data BehaviourAutomaticallySettlesInstantiation
    (c : ConsciousnessCandidate) : Set where

behaviourDoesNotSettleInstantiation :
  ∀ {c} → BehaviourAutomaticallySettlesInstantiation c → ⊥
behaviourDoesNotSettleInstantiation ()


data AbstractTopologyAutomaticallySettlesInstantiation
    (c : ConsciousnessCandidate) : Set where

abstractTopologyDoesNotSettleInstantiation :
  ∀ {c} → AbstractTopologyAutomaticallySettlesInstantiation c → ⊥
abstractTopologyDoesNotSettleInstantiation ()


data SimulationAutomaticallyImpliesInstantiation
    (c : ConsciousnessCandidate) : Set where

simulationDoesNotAutomaticallyImplyInstantiation :
  ∀ {c} → SimulationAutomaticallyImpliesInstantiation c → ⊥
simulationDoesNotAutomaticallyImpliesInstantiation ()

------------------------------------------------------------------------
-- A substrate-sensitive account still does not imply biological exclusivity.
------------------------------------------------------------------------

data SubstrateKind : Set where
  biological digital neuromorphic hybrid unknownSubstrate : SubstrateKind

data SubstrateLabelAutomaticallySettlesConsciousness
    (s : SubstrateKind) : Set where

substrateLabelDoesNotSettleConsciousness :
  ∀ {s} → SubstrateLabelAutomaticallySettlesConsciousness s → ⊥
substrateLabelDoesNotSettleConsciousness ()

------------------------------------------------------------------------
-- Moral/governance authority remains downstream of uncertainty, not of a
-- single ontology paper or behavioural surface.
------------------------------------------------------------------------

data MoralStatusDecision : Set where
  moralStatusOpen moralStatusProtected moralStatusRejected : MoralStatusDecision

data OntologyClaimAutomaticallySettlesMoralStatus : Set where

ontologyClaimDoesNotSettleMoralStatus :
  OntologyClaimAutomaticallySettlesMoralStatus → ⊥
ontologyClaimDoesNotSettleMoralStatus ()

record ConsciousnessAbstractionInstantiationBoundary : Set where
  constructor consciousness-abstraction-instantiation-boundary
  field
    sameBehaviourImpliesSamePhysicalConstitution : Bool
    sameBehaviourImpliesSamePhysicalConstitutionIsFalse :
      sameBehaviourImpliesSamePhysicalConstitution ≡ false
    sameAbstractTopologyImpliesSameInstantiation : Bool
    sameAbstractTopologyImpliesSameInstantiationIsFalse :
      sameAbstractTopologyImpliesSameInstantiation ≡ false
    simulationImpliesInstantiation : Bool
    simulationImpliesInstantiationIsFalse : simulationImpliesInstantiation ≡ false
    substrateSensitiveMeansBiologyOnly : Bool
    substrateSensitiveMeansBiologyOnlyIsFalse : substrateSensitiveMeansBiologyOnly ≡ false
    oneOntologyPaperSettlesMoralStatus : Bool
    oneOntologyPaperSettlesMoralStatusIsFalse : oneOntologyPaperSettlesMoralStatus ≡ false
    reading : String

canonicalConsciousnessAbstractionInstantiationBoundary :
  ConsciousnessAbstractionInstantiationBoundary
canonicalConsciousnessAbstractionInstantiationBoundary =
  consciousness-abstraction-instantiation-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    "Behavioural simulation, abstract causal topology, physical constitution, consciousness-instantiation status and moral-status policy remain distinct. Substrate sensitivity does not itself entail biological exclusivity, and no single ontology claim is promoted directly into moral or governance authority."
