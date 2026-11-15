module DASHI.Culture.ColonialTheatreSensoryAccessExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- COLONIAL THEATRE SENSORY / PARTICIPATORY ACCESS
--
-- Admission is only one access coordinate.  This finite fixture isolates the
-- structural fact that the same nominal entry status can coexist with distinct
-- visual/aural/participatory access.  The fixture is DASHI-owned; surrounding
-- scholarship motivates the question but is not credited with the theorem.
------------------------------------------------------------------------

data TheatreAccessState : Set where
  admittedFullSensory : TheatreAccessState
  admittedMitigatedAural : TheatreAccessState

data EntryStatus : Set where
  admitted : EntryStatus

data VisualAccess : Set where
  directVisual : VisualAccess
  noDirectVisual : VisualAccess

data AuralAccess : Set where
  audible : AuralAccess

data ParticipationAccess : Set where
  audienceOnly : ParticipationAccess
  liminalOrServicePosition : ParticipationAccess

data SensoryAccessCode : Set where
  fullVisualAuralAudience : SensoryAccessCode
  auralMitigatedLiminal : SensoryAccessCode

entryStatus : TheatreAccessState → EntryStatus
entryStatus _ = admitted

visualAccess : TheatreAccessState → VisualAccess
visualAccess admittedFullSensory = directVisual
visualAccess admittedMitigatedAural = noDirectVisual

auralAccess : TheatreAccessState → AuralAccess
auralAccess _ = audible

participationAccess : TheatreAccessState → ParticipationAccess
participationAccess admittedFullSensory = audienceOnly
participationAccess admittedMitigatedAural = liminalOrServicePosition

sensoryAccessCode : TheatreAccessState → SensoryAccessCode
sensoryAccessCode admittedFullSensory = fullVisualAuralAudience
sensoryAccessCode admittedMitigatedAural = auralMitigatedLiminal

sensoryAccessDiffers :
  sensoryAccessCode admittedFullSensory
  ≡ sensoryAccessCode admittedMitigatedAural → ⊥
sensoryAccessDiffers ()

EntryDoesNotRecoverSensoryAccess : Set
EntryDoesNotRecoverSensoryAccess =
  INF.FactorsThrough entryStatus sensoryAccessCode

entryDoesNotRecoverSensoryAccess :
  EntryDoesNotRecoverSensoryAccess → ⊥
entryDoesNotRecoverSensoryAccess =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      admittedFullSensory
      admittedMitigatedAural
      refl
      sensoryAccessDiffers)

data EntryImpliesVisualEqualityPermission : Set where

data SkilledContributionImpliesFreedomPermission : Set where

entryDoesNotImplyVisualEquality : EntryImpliesVisualEqualityPermission → ⊥
entryDoesNotImplyVisualEquality ()

skilledContributionDoesNotImplyFreedom : SkilledContributionImpliesFreedomPermission → ⊥
skilledContributionDoesNotImplyFreedom ()

record SensoryAccessCoordinateDemand : Set where
  constructor sensory-access-coordinate-demand
  field
    entryCoordinateRequired : Bool
    spatialLocationRequired : Bool
    visualAccessRequired : Bool
    auralAccessRequired : Bool
    languageIntelligibilityRequired : Bool
    backstageServiceRouteRequired : Bool
    participationRoleRequired : Bool

canonicalSensoryAccessCoordinateDemand : SensoryAccessCoordinateDemand
canonicalSensoryAccessCoordinateDemand =
  sensory-access-coordinate-demand
    true true true true true true true

record ColonialTheatreSensoryAccessBoundary : Set where
  constructor colonial-theatre-sensory-access-boundary
  field
    admissionExhaustsAccess : Bool
    admissionExhaustsAccessIsFalse : admissionExhaustsAccess ≡ false
    auralAccessImpliesVisualAccess : Bool
    auralAccessImpliesVisualAccessIsFalse : auralAccessImpliesVisualAccess ≡ false
    productiveSkillImpliesMaterialFreedom : Bool
    productiveSkillImpliesMaterialFreedomIsFalse :
      productiveSkillImpliesMaterialFreedom ≡ false
    sensoryCoordinatesMayRefineVenueAccess : Bool
    sensoryCoordinatesMayRefineVenueAccessIsTrue :
      sensoryCoordinatesMayRefineVenueAccess ≡ true

canonicalColonialTheatreSensoryAccessBoundary : ColonialTheatreSensoryAccessBoundary
canonicalColonialTheatreSensoryAccessBoundary =
  colonial-theatre-sensory-access-boundary
    false refl
    false refl
    false refl
    true refl
