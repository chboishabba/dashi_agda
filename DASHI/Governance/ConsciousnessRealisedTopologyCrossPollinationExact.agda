module DASHI.Governance.ConsciousnessRealisedTopologyCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.DeclaredRealisedInteractionTopologyExact as Runtime
import DASHI.Core.SharedStateCoalitionReachableEffectExact as Shared
import DASHI.Governance.ConsciousnessAbstractionInstantiationBoundaryExact as Consciousness
import DASHI.Governance.Lerchner2026AbstractionFallacySourceBridgeExact as Lerchner
import DASHI.Biology.ConsciousAccessNetworkRegression as Access

------------------------------------------------------------------------
-- CONSCIOUSNESS / REALISED-TOPOLOGY CROSS-POLLINATION
--
-- Refines the previous behavioural/computational/physical/phenomenal/moral
-- decomposition by splitting the computational layer into:
--
--   declared abstraction != realised runtime causal/interaction topology.
--
-- This is important whenever agents discover new communication methods through
-- shared state.  A consciousness theory that reasons only over the nominal
-- software graph may therefore be too coarse even before the physical-substrate
-- question is reached.
------------------------------------------------------------------------

data AssayLayer : Set where
  declaredComputationLayer
  realisedInteractionLayer
  behaviourLayer
  physicalConstitutionLayer
  phenomenalInstantiationLayer
  moralGovernanceLayer
  : AssayLayer

record RefinedConsciousnessAssay : Set where
  constructor refined-consciousness-assay
  field
    declaredComputationReference : String
    realisedInteractionReference : String
    behaviourReference : String
    physicalConstitutionReference : String
    phenomenalClaimReference : String
    moralGovernanceReference : String

------------------------------------------------------------------------
-- Canonical imported boundaries.
------------------------------------------------------------------------

runtimeBoundary : Runtime.DeclaredRealisedInteractionBoundary
runtimeBoundary = Runtime.canonicalDeclaredRealisedInteractionBoundary

consciousnessBoundary : Consciousness.ConsciousnessAbstractionInstantiationBoundary
consciousnessBoundary = Consciousness.canonicalConsciousnessAbstractionInstantiationBoundary

lerchnerBoundary : Lerchner.LerchnerAbstractionFallacyBoundary
lerchnerBoundary = Lerchner.canonicalLerchnerAbstractionFallacyBoundary

consciousAccessRegression : Access.ConsciousAccessNetworkRegression
consciousAccessRegression = Access.canonicalConsciousAccessNetworkRegression

sharedStateBoundary : Shared.SharedStateCoalitionBoundary
sharedStateBoundary = Shared.canonicalSharedStateCoalitionBoundary

------------------------------------------------------------------------
-- The conscious-access tranche already refuses single ignition / access
-- structure -> phenomenal identity.  The new runtime layer adds another
-- non-collapse before physical-instantiation questions are reached.
------------------------------------------------------------------------

noPhenomenalIdentityFromAccessNetwork :
  Access.noPhenomenalIdentityPromotion consciousAccessRegression ≡ false
noPhenomenalIdentityFromAccessNetwork = refl

runtimeTopologyNotFixedByDeclaredInterface :
  Runtime.declaredInterfaceDeterminesRealisedTopology runtimeBoundary ≡ false
runtimeTopologyNotFixedByDeclaredInterface = refl

sameAbstractTopologyNotEnoughForInstantiation :
  Consciousness.sameAbstractTopologyImpliesSameInstantiation consciousnessBoundary ≡ false
sameAbstractTopologyNotEnoughForInstantiation = refl

------------------------------------------------------------------------
-- Burden on substrate-sensitive theories.
------------------------------------------------------------------------
-- A theory may claim that physical constitution matters, but deployment-level
-- application still needs to say which physical coordinates matter AND which
-- realised interaction topology those coordinates instantiate.  No constructor
-- here promotes a nominal architecture label into either answer.
------------------------------------------------------------------------

record PhysicalInstantiationDiscriminator : Set where
  constructor physical-instantiation-discriminator
  field
    relevantPhysicalCoordinateReference : String
    realisedTopologyReference : String
    measurementReference : String
    competingTheorySeparationReference : String
    provenanceReference : String
    validationReference : String

record ConsciousnessRealisedTopologyBoundary : Set where
  constructor consciousness-realised-topology-boundary
  field
    nominalSoftwareGraphEqualsRealisedComputation : Bool
    nominalSoftwareGraphEqualsRealisedComputationIsFalse :
      nominalSoftwareGraphEqualsRealisedComputation ≡ false
    emergentCommunicationProvesConsciousness : Bool
    emergentCommunicationProvesConsciousnessIsFalse :
      emergentCommunicationProvesConsciousness ≡ false
    emergentCommunicationProvesNoConsciousness : Bool
    emergentCommunicationProvesNoConsciousnessIsFalse :
      emergentCommunicationProvesNoConsciousness ≡ false
    realisedCausalComplexitySettlesPhenomenalInstantiation : Bool
    realisedCausalComplexitySettlesPhenomenalInstantiationIsFalse :
      realisedCausalComplexitySettlesPhenomenalInstantiation ≡ false
    physicalTheoryNeedsCoordinateLevelDiscriminators : Bool
    physicalTheoryNeedsCoordinateLevelDiscriminatorsIsTrue :
      physicalTheoryNeedsCoordinateLevelDiscriminators ≡ true
    moralTreatmentRemainsSeparateFromOntology : Bool
    moralTreatmentRemainsSeparateFromOntologyIsTrue :
      moralTreatmentRemainsSeparateFromOntology ≡ true
    reading : String

canonicalConsciousnessRealisedTopologyBoundary : ConsciousnessRealisedTopologyBoundary
canonicalConsciousnessRealisedTopologyBoundary =
  consciousness-realised-topology-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    "The consciousness assay is refined to declared computation -> realised interaction topology -> behaviour -> physical constitution -> phenomenal-instantiation claim -> moral/governance treatment, with no automatic promotions. Emergent agent communication shows that deployed causal topology may exceed the nominal interface, but neither proves nor disproves consciousness. Substrate-sensitive theories still owe coordinate-level physical discriminators, and moral policy remains separately governed."
