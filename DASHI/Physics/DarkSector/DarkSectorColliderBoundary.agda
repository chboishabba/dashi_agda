module DASHI.Physics.DarkSector.DarkSectorColliderBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.DarkSector.SectorCarrier as Sector
import DASHI.Physics.DarkSector.GaugeSingletPortal as Portal
import DASHI.Physics.DarkSector.HiggsPortalDecay as Decay
import DASHI.Physics.DarkSector.MetastableLifetime as Lifetime
import DASHI.Physics.DarkSector.BoostedDecayGeometry as Boost
import DASHI.Physics.DarkSector.DisplacedVertex as Vertex
import DASHI.Physics.DarkSector.TriggerCensoring as Trigger
import DASHI.Physics.DarkSector.DarkSectorColliderSourceAtlas as Sources

------------------------------------------------------------------------
-- The exact finite collider theorem spine requested by the attached tranche.
-- Each implication is represented by a typed witness; continuum amplitudes,
-- exponential decay, detector simulation, and empirical inference remain
-- outside the promoted finite theorem surface.

record DarkSectorColliderBoundary : Set where
  field
    sectorCarrierBoundary : Sector.SectorCarrierBoundary
    gaugeSingletPortalBoundary : Portal.GaugeSingletPortalBoundary
    higgsPortalDecayBoundary : Decay.HiggsPortalDecayBoundary
    metastableLifetimeBoundary : Lifetime.MetastableLifetimeBoundary
    boostedDecayGeometryBoundary : Boost.BoostedDecayGeometryBoundary
    displacedVertexBoundary : Vertex.DisplacedVertexBoundary
    triggerCensoringBoundary : Trigger.TriggerCensoringBoundary

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
    ; portalAllowedWitness =
        Portal.quadraticHiggsPortalIsAllowed
    ; hiddenIntermediateWitness =
        Decay.canonicalVisiblePortalChain
    ; finiteLifetimeWitness =
        Lifetime.canonicalWidthLifetimeReciprocal
    ; hiddenUntilTerminalAgeWitness =
        refl
    ; visibleAtTerminalAgeWitness =
        Lifetime.visibleAtTerminalAge
    ; nonzeroBoostedDisplacementWitness =
        Boost.canonicalLaboratoryDisplacementIsEight
    ; displacedVertexWitness =
        Vertex.canonicalEventIsDisplacedVertex
    ; promptTriggerRejectsWitness =
        Trigger.canonicalPromptTriggerRejectsDisplacedSignal
    ; displacedTriggerAcceptsWitness =
        Trigger.canonicalLLPTriggerAcceptsDisplacedSignal
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
