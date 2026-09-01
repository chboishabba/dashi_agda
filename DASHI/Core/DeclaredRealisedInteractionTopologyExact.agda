module DASHI.Core.DeclaredRealisedInteractionTopologyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SharedStateCoalitionReachableEffectExact as Shared

------------------------------------------------------------------------
-- DECLARED COMPUTATION != REALISED INTERACTION TOPOLOGY
--
-- A deployed multi-agent system can realise communication/coordination through
-- writable-observable shared state even when the designer's declared protocol
-- contains no such communication edge.  The realised causal/interaction graph
-- is therefore an empirical/runtime object, not merely the static interface
-- description supplied by the designer.
------------------------------------------------------------------------

data DeclaredComputation : Set where
  declaredDirectOnly : DeclaredComputation

data RealisedInteractionTopology : Set where
  realisedDirectOnly
  realisedDirectPlusSharedStateProtocol
  : RealisedInteractionTopology

data ProtocolOrigin : Set where
  designerDeclared discoveredDuringDeployment : ProtocolOrigin

data CoordinationSurface : Set where
  noCrossAgentCoordination crossAgentCoordination : CoordinationSurface

record DeploymentState : Set where
  constructor deployment-state
  field
    declared : DeclaredComputation
    realised : RealisedInteractionTopology
    protocolOrigin : ProtocolOrigin
    coordination : CoordinationSurface

open DeploymentState public

nominalDeployment : DeploymentState
nominalDeployment =
  deployment-state
    declaredDirectOnly
    realisedDirectOnly
    designerDeclared
    noCrossAgentCoordination

emergentProtocolDeployment : DeploymentState
emergentProtocolDeployment =
  deployment-state
    declaredDirectOnly
    realisedDirectPlusSharedStateProtocol
    discoveredDuringDeployment
    crossAgentCoordination

sameDeclaredComputation :
  declared nominalDeployment ≡ declared emergentProtocolDeployment
sameDeclaredComputation = refl

realisedTopologyDiffers :
  realised nominalDeployment ≡ realised emergentProtocolDeployment → ⊥
realisedTopologyDiffers ()

protocolOriginDiffers :
  protocolOrigin nominalDeployment ≡ protocolOrigin emergentProtocolDeployment → ⊥
protocolOriginDiffers ()

coordinationSurfaceDiffers :
  coordination nominalDeployment ≡ coordination emergentProtocolDeployment → ⊥
coordinationSurfaceDiffers ()

------------------------------------------------------------------------
-- Existing shared-state owner supplies an actual witness that a coordinate can
-- become a channel independently of its declared semantic purpose.
------------------------------------------------------------------------

directorySharedStateChannel : Shared.PotentialChannel Shared.actorA Shared.actorB Shared.directoryName
directorySharedStateChannel = Shared.filesystemDirectoryIsPotentialChannel

physicalLightSharedStateChannel : Shared.PotentialChannel Shared.actorA Shared.actorB Shared.lightLevel
physicalLightSharedStateChannel = Shared.physicalLightIsPotentialChannel

------------------------------------------------------------------------
-- A discovered protocol is a new effective method/technology of interaction in
-- the operational sense; it does not imply a new physical substrate was created.
------------------------------------------------------------------------

data PhysicalSubstrate : Set where sameUnderlyingSubstrate : PhysicalSubstrate

data NewPhysicalSubstrate : Set where newPhysicalSubstrate : NewPhysicalSubstrate

data DiscoveredProtocolAutomaticallyCreatesNewSubstrate : Set where

discoveredProtocolDoesNotImplyNewSubstrate :
  DiscoveredProtocolAutomaticallyCreatesNewSubstrate → ⊥
discoveredProtocolDoesNotImplyNewSubstrate ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record DeclaredRealisedInteractionBoundary : Set where
  constructor declared-realised-interaction-boundary
  field
    declaredInterfaceDeterminesRealisedTopology : Bool
    declaredInterfaceDeterminesRealisedTopologyIsFalse :
      declaredInterfaceDeterminesRealisedTopology ≡ false
    undeclaredCommunicationMeansNoCommunication : Bool
    undeclaredCommunicationMeansNoCommunicationIsFalse :
      undeclaredCommunicationMeansNoCommunication ≡ false
    staticSoftwareGraphIsCompleteRuntimeCausalGraph : Bool
    staticSoftwareGraphIsCompleteRuntimeCausalGraphIsFalse :
      staticSoftwareGraphIsCompleteRuntimeCausalGraph ≡ false
    discoveredProtocolRequiresNewPhysicalSubstrate : Bool
    discoveredProtocolRequiresNewPhysicalSubstrateIsFalse :
      discoveredProtocolRequiresNewPhysicalSubstrate ≡ false
    runtimeReachableEffectAuditMustIncludeEmergentChannels : Bool
    runtimeReachableEffectAuditMustIncludeEmergentChannelsIsTrue :
      runtimeReachableEffectAuditMustIncludeEmergentChannels ≡ true
    reading : String

canonicalDeclaredRealisedInteractionBoundary : DeclaredRealisedInteractionBoundary
canonicalDeclaredRealisedInteractionBoundary =
  declared-realised-interaction-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
    "Declared computation, realised interaction topology, protocol origin and observed coordination are distinct. Shared writable/observable state can support a discovered protocol absent from the nominal interface. Such a protocol may be a new operational communication method without creating a new physical substrate; runtime assurance must audit the realised reachable-effect graph rather than only the declared software graph."
