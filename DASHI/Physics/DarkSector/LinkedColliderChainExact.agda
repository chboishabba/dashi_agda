module DASHI.Physics.DarkSector.LinkedColliderChainExact where

open import DASHI.Core.Prelude

import DASHI.Physics.DarkSector.GaugeSingletPortal as Portal
import DASHI.Physics.DarkSector.HiggsPortalDecay as Decay
import DASHI.Physics.DarkSector.MetastableLifetime as Lifetime
import DASHI.Physics.DarkSector.BoostedDecayGeometry as Boost
import DASHI.Physics.DarkSector.DisplacedVertex as Vertex
import DASHI.Physics.DarkSector.TriggerCensoring as Trigger

------------------------------------------------------------------------
-- One dependent canonical collider chain.  Each later stage is indexed by the
-- earlier stage and carries the equality that connects its numerical datum to
-- the preceding datum.  This repairs the weaker product-of-independent-witness
-- interpretation of the original aggregate boundary.

record PortalProduction : Set where
  constructor portalProduction
  field
    portalOperator : Portal.PortalOperator
    portalIsAllowed : Portal.portalAllowed portalOperator ≡ true
    visiblePortalChain : Decay.VisiblePortalChain

open PortalProduction public

record MetastablePropagation
  (production : PortalProduction) : Set where
  constructor metastablePropagation
  field
    lifetimeDatum : Lifetime.ScaledDecayDatum
    reciprocalLaw : Lifetime.scaledReciprocalLaw lifetimeDatum
    hiddenAtPreterminalAge :
      Lifetime.visibilityAtAge Lifetime.ageThree
      ≡
      Lifetime.hiddenPhase
    visibleAtTerminalAge :
      Lifetime.visibilityAtAge Lifetime.ageFour
      ≡
      Lifetime.visibleDecayPhase

open MetastablePropagation public

record BoostedPropagation
  {production : PortalProduction}
  (metastable : MetastablePropagation production) : Set where
  constructor boostedPropagation
  field
    boostedDatum : Boost.BoostedDecayDatum
    properLifetimeMatches :
      Boost.properLifetimeUnits boostedDatum
      ≡
      Lifetime.lifetimeUnits (lifetimeDatum metastable)
    displacementPredecessor : Nat
    displacementIsPositive :
      Boost.laboratoryDisplacement boostedDatum
      ≡
      suc displacementPredecessor

open BoostedPropagation public

record ReconstructedDetection
  {production : PortalProduction}
  {metastable : MetastablePropagation production}
  (boosted : BoostedPropagation metastable) : Set where
  constructor reconstructedDetection
  field
    reconstructedEvent : Vertex.VertexEvent
    eventDisplacementMatches :
      Vertex.vertexDisplacement reconstructedEvent
      ≡
      Boost.laboratoryDisplacement (boostedDatum boosted)
    eventIsDisplaced :
      Vertex.isDisplacedVertex reconstructedEvent ≡ true
    promptTriggerRejects :
      Trigger.promptTrigger reconstructedEvent ≡ Trigger.rejectEvent
    llpTriggerAccepts :
      Trigger.llpTrigger reconstructedEvent ≡ Trigger.acceptEvent

open ReconstructedDetection public

record LinkedColliderChain : Set where
  constructor linkedColliderChain
  field
    productionStage : PortalProduction
    metastableStage : MetastablePropagation productionStage
    boostedStage : BoostedPropagation metastableStage
    detectionStage : ReconstructedDetection boostedStage

open LinkedColliderChain public

canonicalPortalProduction : PortalProduction
canonicalPortalProduction =
  portalProduction
    Portal.canonicalQuadraticHiggsPortal
    Portal.quadraticHiggsPortalIsAllowed
    Decay.canonicalVisiblePortalChain

canonicalMetastablePropagation :
  MetastablePropagation canonicalPortalProduction
canonicalMetastablePropagation =
  metastablePropagation
    Lifetime.canonicalLongLivedDecay
    Lifetime.canonicalWidthLifetimeReciprocal
    refl
    Lifetime.visibleAtTerminalAge

canonicalBoostedPropagation :
  BoostedPropagation canonicalMetastablePropagation
canonicalBoostedPropagation =
  boostedPropagation
    Boost.canonicalBoostedDecay
    Boost.lifetimeMatchesScaledDecayDatum
    7
    refl

canonicalReconstructedDetection :
  ReconstructedDetection canonicalBoostedPropagation
canonicalReconstructedDetection =
  reconstructedDetection
    Vertex.canonicalDisplacedEvent
    Vertex.canonicalDisplacementMatchesBoostedGeometry
    Vertex.canonicalEventIsDisplacedVertex
    Trigger.canonicalPromptTriggerRejectsDisplacedSignal
    Trigger.canonicalLLPTriggerAcceptsDisplacedSignal

canonicalLinkedColliderChain : LinkedColliderChain
canonicalLinkedColliderChain =
  linkedColliderChain
    canonicalPortalProduction
    canonicalMetastablePropagation
    canonicalBoostedPropagation
    canonicalReconstructedDetection

------------------------------------------------------------------------
-- Projection theorems from one coherent chain, rather than unrelated fixed
-- witnesses assembled only at the outer boundary.

linkedPortalAllowed :
  Portal.portalAllowed
    (portalOperator
      (productionStage canonicalLinkedColliderChain))
  ≡
  true
linkedPortalAllowed =
  portalIsAllowed
    (productionStage canonicalLinkedColliderChain)

linkedVisibleIntermediate : Decay.VisiblePortalChain
linkedVisibleIntermediate =
  visiblePortalChain
    (productionStage canonicalLinkedColliderChain)

linkedReciprocalLifetime :
  Lifetime.scaledReciprocalLaw
    (lifetimeDatum
      (metastableStage canonicalLinkedColliderChain))
linkedReciprocalLifetime =
  reciprocalLaw
    (metastableStage canonicalLinkedColliderChain)

linkedLifetimeMatchesBoost :
  Boost.properLifetimeUnits
    (boostedDatum
      (boostedStage canonicalLinkedColliderChain))
  ≡
  Lifetime.lifetimeUnits
    (lifetimeDatum
      (metastableStage canonicalLinkedColliderChain))
linkedLifetimeMatchesBoost =
  properLifetimeMatches
    (boostedStage canonicalLinkedColliderChain)

linkedDisplacementMatchesEvent :
  Vertex.vertexDisplacement
    (reconstructedEvent
      (detectionStage canonicalLinkedColliderChain))
  ≡
  Boost.laboratoryDisplacement
    (boostedDatum
      (boostedStage canonicalLinkedColliderChain))
linkedDisplacementMatchesEvent =
  eventDisplacementMatches
    (detectionStage canonicalLinkedColliderChain)

linkedEventIsDisplaced :
  Vertex.isDisplacedVertex
    (reconstructedEvent
      (detectionStage canonicalLinkedColliderChain))
  ≡
  true
linkedEventIsDisplaced =
  eventIsDisplaced
    (detectionStage canonicalLinkedColliderChain)

linkedPromptRejects :
  Trigger.promptTrigger
    (reconstructedEvent
      (detectionStage canonicalLinkedColliderChain))
  ≡
  Trigger.rejectEvent
linkedPromptRejects =
  promptTriggerRejects
    (detectionStage canonicalLinkedColliderChain)

linkedLLPAccepts :
  Trigger.llpTrigger
    (reconstructedEvent
      (detectionStage canonicalLinkedColliderChain))
  ≡
  Trigger.acceptEvent
linkedLLPAccepts =
  llpTriggerAccepts
    (detectionStage canonicalLinkedColliderChain)

record LinkedColliderChainBoundary : Set where
  constructor linkedColliderChainBoundary
  field
    allowedPortalAloneGuaranteesDownstreamChain : Bool
    allowedPortalAloneGuaranteesDownstreamChainIsFalse :
      allowedPortalAloneGuaranteesDownstreamChain ≡ false

    linkedFiniteChainIsContinuumColliderAmplitude : Bool
    linkedFiniteChainIsContinuumColliderAmplitudeIsFalse :
      linkedFiniteChainIsContinuumColliderAmplitude ≡ false

    linkedFiniteChainIsObservedDarkSectorSignal : Bool
    linkedFiniteChainIsObservedDarkSectorSignalIsFalse :
      linkedFiniteChainIsObservedDarkSectorSignal ≡ false

open LinkedColliderChainBoundary public

canonicalLinkedColliderChainBoundary : LinkedColliderChainBoundary
canonicalLinkedColliderChainBoundary =
  linkedColliderChainBoundary false refl false refl false refl
