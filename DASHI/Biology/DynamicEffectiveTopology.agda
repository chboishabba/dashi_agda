module DASHI.Biology.DynamicEffectiveTopology where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- State-mediated effective topology over fixed anatomy.
--
-- Source-facing references:
-- R. Matthew Hutchison et al., "Dynamic functional connectivity: Promise,
-- issues, and interpretations", DOI 10.1016/j.neuroimage.2013.05.079.
-- Gustavo Deco et al., "The Dynamic Brain: From Spiking Neurons to Neural
-- Masses and Cortical Fields", DOI 10.1371/journal.pcbi.0040100.

data Node : Set where
  sensoryNode : Node
  associationNode : Node
  planningNode : Node

data AnatomicalEdge : Node → Node → Set where
  sensoryAssociationEdge : AnatomicalEdge sensoryNode associationNode
  associationPlanningEdge : AnatomicalEdge associationNode planningNode
  sensoryPlanningEdge : AnatomicalEdge sensoryNode planningNode

data ElectrochemicalState : Set where
  inhibitedState : ElectrochemicalState
  permissiveState : ElectrochemicalState
  recurrentState : ElectrochemicalState

edgeOpen :
  ∀ {a b : Node} →
  ElectrochemicalState →
  AnatomicalEdge a b →
  Bool
edgeOpen inhibitedState sensoryAssociationEdge = false
edgeOpen inhibitedState associationPlanningEdge = false
edgeOpen inhibitedState sensoryPlanningEdge = false
edgeOpen permissiveState sensoryAssociationEdge = true
edgeOpen permissiveState associationPlanningEdge = false
edgeOpen permissiveState sensoryPlanningEdge = false
edgeOpen recurrentState sensoryAssociationEdge = true
edgeOpen recurrentState associationPlanningEdge = true
edgeOpen recurrentState sensoryPlanningEdge = false

record EffectiveEdge (s : ElectrochemicalState) (a b : Node) : Set where
  constructor effectiveEdge
  field
    anatomical : AnatomicalEdge a b
    openWitness : edgeOpen s anatomical ≡ true

open EffectiveEdge public

data Reachable (s : ElectrochemicalState) : Node → Node → Set where
  directReach :
    ∀ {a b : Node} →
    EffectiveEdge s a b →
    Reachable s a b

  composeReach :
    ∀ {a b c : Node} →
    Reachable s a b →
    Reachable s b c →
    Reachable s a c

permissiveSensoryAssociation :
  EffectiveEdge permissiveState sensoryNode associationNode
permissiveSensoryAssociation =
  effectiveEdge sensoryAssociationEdge refl

recurrentSensoryAssociation :
  EffectiveEdge recurrentState sensoryNode associationNode
recurrentSensoryAssociation =
  effectiveEdge sensoryAssociationEdge refl

recurrentAssociationPlanning :
  EffectiveEdge recurrentState associationNode planningNode
recurrentAssociationPlanning =
  effectiveEdge associationPlanningEdge refl

recurrentSensoryPlanningReach :
  Reachable recurrentState sensoryNode planningNode
recurrentSensoryPlanningReach =
  composeReach
    (directReach recurrentSensoryAssociation)
    (directReach recurrentAssociationPlanning)

------------------------------------------------------------------------
-- Same anatomy, different state, different reachability.

inhibitedAssociationPlanningImpossible :
  EffectiveEdge inhibitedState associationNode planningNode → ⊥
inhibitedAssociationPlanningImpossible (effectiveEdge associationPlanningEdge ())

inhibitedSensoryAssociationImpossible :
  EffectiveEdge inhibitedState sensoryNode associationNode → ⊥
inhibitedSensoryAssociationImpossible (effectiveEdge sensoryAssociationEdge ())

record EffectiveTopologyContrast : Set where
  constructor effectiveTopologyContrast
  field
    sameAnatomicalCarrier : Bool
    sameAnatomicalCarrierIsTrue : sameAnatomicalCarrier ≡ true

    inhibitedDirectClosed :
      EffectiveEdge inhibitedState associationNode planningNode → ⊥

    recurrentDirectOpen :
      EffectiveEdge recurrentState associationNode planningNode

    recurrentTwoStepReach :
      Reachable recurrentState sensoryNode planningNode

open EffectiveTopologyContrast public

canonicalEffectiveTopologyContrast : EffectiveTopologyContrast
canonicalEffectiveTopologyContrast =
  effectiveTopologyContrast
    true refl
    inhibitedAssociationPlanningImpossible
    recurrentAssociationPlanning
    recurrentSensoryPlanningReach

record DynamicTopologyBoundary : Set where
  constructor dynamicTopologyBoundary
  field
    anatomyAloneDeterminesEffectiveReach : Bool
    anatomyAloneDeterminesEffectiveReachIsFalse :
      anatomyAloneDeterminesEffectiveReach ≡ false

    functionalEdgeIsAnatomicalIdentity : Bool
    functionalEdgeIsAnatomicalIdentityIsFalse :
      functionalEdgeIsAnatomicalIdentity ≡ false

canonicalDynamicTopologyBoundary : DynamicTopologyBoundary
canonicalDynamicTopologyBoundary =
  dynamicTopologyBoundary false refl false refl
