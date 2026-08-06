module DASHI.Physics.DarkSector.DarkSectorColliderRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.DarkSector.SectorCarrier as Sector
import DASHI.Physics.DarkSector.GaugeSingletPortal as Portal
import DASHI.Physics.DarkSector.HiggsPortalDecay as Decay
import DASHI.Physics.DarkSector.MetastableLifetime as Lifetime
import DASHI.Physics.DarkSector.BoostedDecayGeometry as Boost
import DASHI.Physics.DarkSector.DisplacedVertex as Vertex
import DASHI.Physics.DarkSector.TriggerCensoring as Trigger
import DASHI.Physics.DarkSector.DarkSectorColliderSourceAtlas as Sources
import DASHI.Physics.DarkSector.DarkSectorColliderBoundary as Boundary

colliderBoundaryExists : Boundary.DarkSectorColliderBoundary
colliderBoundaryExists = Boundary.canonicalDarkSectorColliderBoundary

sectorRegression :
  Sector.classifyDetectorVisibility Sector.canonicalHiddenLLP
  ≡
  Sector.detectorVisible
sectorRegression = refl

portalRegression :
  Portal.portalAllowed Portal.canonicalQuadraticHiggsPortal ≡ true
portalRegression = refl

decayGraphRegression : Decay.VisiblePortalChain
decayGraphRegression = Decay.canonicalVisiblePortalChain

lifetimeRegression :
  Lifetime.widthUnits Lifetime.canonicalLongLivedDecay
  *
  Lifetime.lifetimeUnits Lifetime.canonicalLongLivedDecay
  ≡
  Lifetime.reciprocalScale Lifetime.canonicalLongLivedDecay
lifetimeRegression = refl

metastabilityRegression :
  Lifetime.visibilityAtAge Lifetime.ageThree ≡ Lifetime.hiddenPhase
  ×
  Lifetime.visibilityAtAge Lifetime.ageFour ≡ Lifetime.visibleDecayPhase
metastabilityRegression = refl , refl

boostedDisplacementRegression :
  Boost.laboratoryDisplacement Boost.canonicalBoostedDecay ≡ 8
boostedDisplacementRegression = refl

vertexRegression :
  Vertex.vertexDisplacement Vertex.canonicalDisplacedEvent ≡ 8
  ×
  Vertex.isDisplacedVertex Vertex.canonicalDisplacedEvent ≡ true
vertexRegression = refl , refl

triggerRegression :
  Trigger.promptTrigger Vertex.canonicalDisplacedEvent ≡ Trigger.rejectEvent
  ×
  Trigger.llpTrigger Vertex.canonicalDisplacedEvent ≡ Trigger.acceptEvent
triggerRegression = refl , refl

censoringRegression :
  Trigger.recordedSignalCount 5 2 0
  ≡
  Trigger.recordedSignalCount 9 1 0
censoringRegression = refl

controlSampleRegression :
  Trigger.promptTrigger
    (Trigger.classEvent Trigger.promptControl)
  ≡
  Trigger.acceptEvent
  ×
  Trigger.llpTrigger
    (Trigger.classEvent Trigger.displacedSignal)
  ≡
  Trigger.acceptEvent
controlSampleRegression = refl , refl

sourceRegression : Sources.canonicalDarkSectorColliderSourceCount ≡ 6
sourceRegression = Sources.canonicalDarkSectorColliderSourceCountIsSix
