module DASHI.Physics.DarkSector.DarkSectorColliderBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.DarkSector.SectorCarrier as Sector
import DASHI.Physics.DarkSector.GaugeSingletPortal as Portal
import DASHI.Physics.DarkSector.HiggsPortalDecay as Decay
import DASHI.Physics.DarkSector.MetastableLifetime as Lifetime
import DASHI.Physics.DarkSector.BoostedDecayGeometry as Boost
import DASHI.Physics.DarkSector.DisplacedVertex as VertexInternal
import DASHI.Physics.DarkSector.TriggerCensoring as TriggerInternal
import DASHI.Physics.DarkSector.LinkedColliderChainExact as Linked
import DASHI.Physics.DarkSector.DarkSectorColliderSourceAtlas as Sources

module Vertex = VertexInternal
module Trigger = TriggerInternal

------------------------------------------------------------------------
-- Collider-facing finite witnesses plus one dependent linked chain.  The
-- original fixed projections remain available for compatibility, but the
-- actual portal -> lifetime -> boost -> event -> trigger relation is carried by
-- LinkedColliderChainExact rather than inferred from a product of unrelated
-- fields.  Continuum amplitudes, exponential decay, detector simulation, and
-- empirical inference remain outside the promoted finite theorem surface.

record DarkSectorColliderBoundary : Set where
  field
    sectorCarrierBoundary : Sector.SectorCarrierBoundary
    gaugeSingletPortalBoundary : Portal.GaugeSingletPortalBoundary
    higgsPortalDecayBoundary : Decay.HiggsPortalDecayBoundary
    metastableLifetimeBoundary : Lifetime.MetastableLifetimeBoundary
    boostedDecayGeometryBoundary : Boost.BoostedDecayGeometryBoundary
    displacedVertexBoundary : Vertex.DisplacedVertexBoundary
    triggerCensoringBoundary : Trigger.TriggerCensoringBoundary
    linkedColliderChainBoundary : Linked.LinkedColliderChainBoundary
    linkedCanonicalChain : Linked.LinkedColliderChain

    portalAllowedWitness :
      Portal.portalAllowed Portal.canonicalQuadraticHiggsPortal ≡ true

    hiddenIntermediateWitness :
      Decay.VisiblePortalChain

    finiteLifetimeWitness :
      Lifetime.scaledReciprocalLaw Lifetime.canonicalLongLivedDecay

    hiddenUntilTerminalAgeWitness :
      Lifetime.visibilityAtAge Lifetime.ageThree ≡ Lifetime.hiddenPhase

    visibleAtTerminalAgeWitness :
      Lifetime.visibilityAtAge Lifetime.ageFour
      ≡
      Lifetime.visibleDecayPhase

    nonzeroBoostedDisplacementWitness :
      Boost.laboratoryDisplacement Boost.canonicalBoostedDecay ≡ 8

    displacedVertexWitness :
      Vertex.isDisplacedVertex Vertex.canonicalDisplacedEvent ≡ true

    promptTriggerRejectsWitness :
      Trigger.promptTrigger Vertex.canonicalDisplacedEvent
      ≡
      Trigger.rejectEvent

    displacedTriggerAcceptsWitness :
      Trigger.llpTrigger Vertex.canonicalDisplacedEvent
      ≡
      Trigger.acceptEvent

    linkedLifetimeToBoostWitness :
      Boost.properLifetimeUnits
        (Linked.boostedDatum
          (Linked.boostedStage linkedCanonicalChain))
      ≡
      Lifetime.lifetimeUnits
        (Linked.lifetimeDatum
          (Linked.metastableStage linkedCanonicalChain))

    linkedBoostToEventWitness :
      Vertex.vertexDisplacement
        (Linked.reconstructedEvent
          (Linked.detectionStage linkedCanonicalChain))
      ≡
      Boost.laboratoryDisplacement
        (Linked.boostedDatum
          (Linked.boostedStage linkedCanonicalChain))

    linkedEventTriggerWitness :
      Trigger.promptTrigger
        (Linked.reconstructedEvent
          (Linked.detectionStage linkedCanonicalChain))
      ≡
      Trigger.rejectEvent
      ×
      Trigger.llpTrigger
        (Linked.reconstructedEvent
          (Linked.detectionStage linkedCanonicalChain))
      ≡
      Trigger.acceptEvent

    censoredNullNonidentifiabilityWitness :
      Trigger.recordedSignalCount 5 2 0
      ≡
      Trigger.recordedSignalCount 9 1 0

    darkSectorColliderSourceCountIsSix :
      Sources.canonicalDarkSectorColliderSourceCount ≡ 6

    finiteEventTopologyIsEvidenceForActualDarkSector : Bool
    finiteEventTopologyIsEvidenceForActualDarkSectorIsFalse :
      finiteEventTopologyIsEvidenceForActualDarkSector ≡ false

    displacedDecayIsDelayedWavefunctionCollapse : Bool
    displacedDecayIsDelayedWavefunctionCollapseIsFalse :
      displacedDecayIsDelayedWavefunctionCollapse ≡ false

open DarkSectorColliderBoundary public

canonicalDarkSectorColliderBoundary : DarkSectorColliderBoundary
canonicalDarkSectorColliderBoundary =
  record
    { sectorCarrierBoundary =
        Sector.canonicalSectorCarrierBoundary
    ; gaugeSingletPortalBoundary =
        Portal.canonicalGaugeSingletPortalBoundary
    ; higgsPortalDecayBoundary =
        Decay.canonicalHiggsPortalDecayBoundary
    ; metastableLifetimeBoundary =
        Lifetime.canonicalMetastableLifetimeBoundary
    ; boostedDecayGeometryBoundary =
        Boost.canonicalBoostedDecayGeometryBoundary
    ; displacedVertexBoundary =
        Vertex.canonicalDisplacedVertexBoundary
    ; triggerCensoringBoundary =
        Trigger.canonicalTriggerCensoringBoundary
    ; linkedColliderChainBoundary =
        Linked.canonicalLinkedColliderChainBoundary
    ; linkedCanonicalChain =
        Linked.canonicalLinkedColliderChain
    ; portalAllowedWitness =
        Linked.linkedPortalAllowed
    ; hiddenIntermediateWitness =
        Linked.linkedVisibleIntermediate
    ; finiteLifetimeWitness =
        Linked.linkedReciprocalLifetime
    ; hiddenUntilTerminalAgeWitness =
        refl
    ; visibleAtTerminalAgeWitness =
        Lifetime.visibleAtTerminalAge
    ; nonzeroBoostedDisplacementWitness =
        Boost.canonicalLaboratoryDisplacementIsEight
    ; displacedVertexWitness =
        Linked.linkedEventIsDisplaced
    ; promptTriggerRejectsWitness =
        Linked.linkedPromptRejects
    ; displacedTriggerAcceptsWitness =
        Linked.linkedLLPAccepts
    ; linkedLifetimeToBoostWitness =
        Linked.linkedLifetimeMatchesBoost
    ; linkedBoostToEventWitness =
        Linked.linkedDisplacementMatchesEvent
    ; linkedEventTriggerWitness =
        Linked.linkedPromptRejects , Linked.linkedLLPAccepts
    ; censoredNullNonidentifiabilityWitness =
        Trigger.recordedNullDoesNotIdentifyProduction
    ; darkSectorColliderSourceCountIsSix =
        Sources.canonicalDarkSectorColliderSourceCountIsSix
    ; finiteEventTopologyIsEvidenceForActualDarkSector =
        false
    ; finiteEventTopologyIsEvidenceForActualDarkSectorIsFalse =
        refl
    ; displacedDecayIsDelayedWavefunctionCollapse =
        false
    ; displacedDecayIsDelayedWavefunctionCollapseIsFalse =
        refl
    }
