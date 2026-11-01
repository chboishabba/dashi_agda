module DASHI.Physics.DarkSector.HiggsPortalDecay where

open import DASHI.Core.Prelude

import DASHI.Physics.DarkSector.GaugeSingletPortal as Portal

------------------------------------------------------------------------
-- Finite decay topology.  Production, portal transition, hidden propagation,
-- and visible/invisible daughters remain distinct nodes and edges.

data ColliderNode : Set where
  protonCollision : ColliderNode
  higgsExcitation : ColliderNode
  hiddenPair : ColliderNode
  visibleDaughterPair : ColliderNode
  invisibleDaughterPair : ColliderNode

data DecayEdge : ColliderNode → ColliderNode → Set where
  produceHiggs : DecayEdge protonCollision higgsExcitation
  higgsThroughPortal : DecayEdge higgsExcitation hiddenPair
  hiddenToVisible : DecayEdge hiddenPair visibleDaughterPair
  hiddenToInvisible : DecayEdge hiddenPair invisibleDaughterPair

record VisiblePortalChain : Set where
  constructor visiblePortalChain
  field
    productionEdge : DecayEdge protonCollision higgsExcitation
    portalEdge : DecayEdge higgsExcitation hiddenPair
    visibleDecayEdge : DecayEdge hiddenPair visibleDaughterPair

open VisiblePortalChain public

record InvisiblePortalChain : Set where
  constructor invisiblePortalChain
  field
    invisibleProductionEdge : DecayEdge protonCollision higgsExcitation
    invisiblePortalEdge : DecayEdge higgsExcitation hiddenPair
    invisibleDecayEdge : DecayEdge hiddenPair invisibleDaughterPair

open InvisiblePortalChain public

canonicalVisiblePortalChain : VisiblePortalChain
canonicalVisiblePortalChain =
  visiblePortalChain produceHiggs higgsThroughPortal hiddenToVisible

canonicalInvisiblePortalChain : InvisiblePortalChain
canonicalInvisiblePortalChain =
  invisiblePortalChain produceHiggs higgsThroughPortal hiddenToInvisible

visibleChainUsesAllowedPortal :
  Portal.portalAllowed Portal.canonicalQuadraticHiggsPortal ≡ true
visibleChainUsesAllowedPortal = Portal.quadraticHiggsPortalIsAllowed

------------------------------------------------------------------------
-- Branch labels keep visible and invisible final states distinct even though
-- both share the same hidden intermediate state.

data DecayBranch : Set where
  visibleBranch : DecayBranch
  invisibleBranch : DecayBranch

branchEndpoint : DecayBranch → ColliderNode
branchEndpoint visibleBranch = visibleDaughterPair
branchEndpoint invisibleBranch = invisibleDaughterPair

visibleAndInvisibleEndpointsAreDistinct :
  branchEndpoint visibleBranch ≡ branchEndpoint invisibleBranch → ⊥
visibleAndInvisibleEndpointsAreDistinct ()

record HiggsPortalDecayBoundary : Set where
  constructor higgsPortalDecayBoundary
  field
    allowedPortalGuaranteesHiggsDecayKinematics : Bool
    allowedPortalGuaranteesHiggsDecayKinematicsIsFalse :
      allowedPortalGuaranteesHiggsDecayKinematics ≡ false

    hiddenIntermediateMustEndInVisibleDaughters : Bool
    hiddenIntermediateMustEndInVisibleDaughtersIsFalse :
      hiddenIntermediateMustEndInVisibleDaughters ≡ false

    finiteDecayGraphComputesBranchingFractions : Bool
    finiteDecayGraphComputesBranchingFractionsIsFalse :
      finiteDecayGraphComputesBranchingFractions ≡ false

open HiggsPortalDecayBoundary public

canonicalHiggsPortalDecayBoundary : HiggsPortalDecayBoundary
canonicalHiggsPortalDecayBoundary =
  higgsPortalDecayBoundary false refl false refl false refl
