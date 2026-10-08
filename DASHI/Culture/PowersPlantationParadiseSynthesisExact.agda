module DASHI.Culture.PowersPlantationParadiseSynthesisExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.CriticalSocialEcologyObserverRegimeExact as Ecology
import DASHI.Core.RelationalHistoryFabricExact as HistoryFabric
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transition
import DASHI.Governance.OptionConeCoercionExact as OptionCone
import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as Power
import DASHI.Governance.RecognitionDistributionRepresentationAxesExact as Fraser
import DASHI.Culture.HistoricalTotalityCriticalTheoryCrossPollinationExact as Totality
import DASHI.Culture.PowersPlantationParadiseSourceAtlasExact as Sources
import DASHI.Culture.ColonialPerformanceStatusNonfactorabilityExact as Performance
import DASHI.Culture.HistoricalArchiveAbsenceNonfactorabilityExact as Archive
import DASHI.Culture.ColonialTheatreAccessAdapterExact as Access

------------------------------------------------------------------------
-- POWERS PLANTATION -> PARADISE? SYNTHESIS
--
-- The question mark is formalised as a projection disagreement, not as a
-- literal claim that a plantation state monotonically transforms into a
-- paradise state.  Cultural visibility, material affordance, redistribution,
-- representation, access and global emancipation remain independent axes.
------------------------------------------------------------------------

data PowersHistoricalState : Set where
  paradiseSurfaceRestrictedMaterial : PowersHistoricalState
  paradiseSurfaceExpandedMaterial : PowersHistoricalState

data ParadiseObserverReading : Set where
  paradiseSurface : ParadiseObserverReading

data MaterialAffordance : Set where
  materiallyRestricted : MaterialAffordance
  materiallyExpanded : MaterialAffordance

paradiseObserver : PowersHistoricalState → ParadiseObserverReading
paradiseObserver _ = paradiseSurface

materialAffordance : PowersHistoricalState → MaterialAffordance
materialAffordance paradiseSurfaceRestrictedMaterial = materiallyRestricted
materialAffordance paradiseSurfaceExpandedMaterial = materiallyExpanded

materialAffordanceDiffers :
  materialAffordance paradiseSurfaceRestrictedMaterial
  ≡ materialAffordance paradiseSurfaceExpandedMaterial → ⊥
materialAffordanceDiffers ()

paradiseObserverCannotRecoverMaterialAffordance :
  INF.FactorsThrough paradiseObserver materialAffordance → ⊥
paradiseObserverCannotRecoverMaterialAffordance =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      paradiseSurfaceRestrictedMaterial
      paradiseSurfaceExpandedMaterial
      refl
      materialAffordanceDiffers)

------------------------------------------------------------------------
-- Existing critical-social-ecology donor theorem: inclusive/liberatory reading
-- is already known not to determine realised material affordance.
------------------------------------------------------------------------

existingObserverAffordanceDonor :
  INF.FactorsThrough Ecology.nominalLiberatoryObserver Ecology.realizedRemain → ⊥
existingObserverAffordanceDonor =
  Ecology.nominalLiberatoryLabelCannotRecoverRealizedAffordance

------------------------------------------------------------------------
-- Fraser axes remain independent under this synthesis.
------------------------------------------------------------------------

recognitionCannotRecoverDistribution :
  INF.FactorsThrough Fraser.recognition Fraser.distribution → ⊥
recognitionCannotRecoverDistribution = Fraser.recognitionCannotRecoverDistribution

distributionCannotRecoverRepresentation :
  INF.FactorsThrough Fraser.distribution Fraser.representation → ⊥
distributionCannotRecoverRepresentation =
  Fraser.distributionCannotRecoverRepresentation

------------------------------------------------------------------------
-- Local option expansion is not global emancipation.
------------------------------------------------------------------------

data ExpansionState : Set where
  localExpandedGloballyRestricted : ExpansionState
  localExpandedGloballyOpen : ExpansionState

data LocalExpansion : Set where
  localOptionExpanded : LocalExpansion

data GlobalEmancipation : Set where
  globalRestrictionRemains : GlobalEmancipation
  globalRestrictionRemoved : GlobalEmancipation

localExpansion : ExpansionState → LocalExpansion
localExpansion _ = localOptionExpanded

globalEmancipation : ExpansionState → GlobalEmancipation
globalEmancipation localExpandedGloballyRestricted = globalRestrictionRemains
globalEmancipation localExpandedGloballyOpen = globalRestrictionRemoved

globalEmancipationDiffers :
  globalEmancipation localExpandedGloballyRestricted
  ≡ globalEmancipation localExpandedGloballyOpen → ⊥
globalEmancipationDiffers ()

localExpansionDoesNotProveGlobalEmancipation :
  INF.FactorsThrough localExpansion globalEmancipation → ⊥
localExpansionDoesNotProveGlobalEmancipation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      localExpandedGloballyRestricted
      localExpandedGloballyOpen
      refl
      globalEmancipationDiffers)

------------------------------------------------------------------------
-- Source / theorem firewall.
------------------------------------------------------------------------

data EpistemicLayer : Set where
  powersSourceClaim : EpistemicLayer
  dashiTheorem : EpistemicLayer

sourceClaimDoesNotBecomeDASHITheorem : powersSourceClaim ≡ dashiTheorem → ⊥
sourceClaimDoesNotBecomeDASHITheorem ()

------------------------------------------------------------------------
-- Cross-pollination receipts: these values expose the imported boundaries so
-- downstream consumers can see exactly which generic owners are being reused.
------------------------------------------------------------------------

sourceBoundary : Sources.PowersSourceBoundary
sourceBoundary = Sources.canonicalPowersSourceBoundary

performanceBoundary : Performance.ColonialPerformanceStatusBoundary
performanceBoundary = Performance.canonicalColonialPerformanceStatusBoundary

archiveBoundary : Archive.HistoricalArchiveBoundary
archiveBoundary = Archive.canonicalHistoricalArchiveBoundary

accessBoundary : Access.ColonialTheatreAccessBoundary
accessBoundary = Access.canonicalColonialTheatreAccessBoundary

observerBoundary : Ecology.ObserverRegimeBoundary
observerBoundary = Ecology.canonicalObserverRegimeBoundary

powerBoundary : Power.SocioTechnicalPowerSelectionBoundary
powerBoundary = Power.canonicalSocioTechnicalPowerSelectionBoundary

participationBoundary : Fraser.ParticipationAxesBoundary
participationBoundary = Fraser.canonicalParticipationAxesBoundary

totalityBoundary : Totality.HistoricalTotalityCriticalTheoryBoundary
totalityBoundary = Totality.canonicalHistoricalTotalityCriticalTheoryBoundary

record PowersPlantationParadiseBoundary : Set where
  constructor powers-plantation-paradise-boundary
  field
    paradiseProjectionEqualsHistoricalCarrier : Bool
    paradiseProjectionEqualsHistoricalCarrierIsFalse :
      paradiseProjectionEqualsHistoricalCarrier ≡ false
    culturalVisibilityImpliesMaterialFreedom : Bool
    culturalVisibilityImpliesMaterialFreedomIsFalse :
      culturalVisibilityImpliesMaterialFreedom ≡ false
    localOptionExpansionImpliesGlobalEmancipation : Bool
    localOptionExpansionImpliesGlobalEmancipationIsFalse :
      localOptionExpansionImpliesGlobalEmancipation ≡ false
    archiveSilenceImpliesHistoricalAbsence : Bool
    archiveSilenceImpliesHistoricalAbsenceIsFalse :
      archiveSilenceImpliesHistoricalAbsence ≡ false
    performanceImpliesSocialOccupancy : Bool
    performanceImpliesSocialOccupancyIsFalse :
      performanceImpliesSocialOccupancy ≡ false
    performanceImpliesEndorsement : Bool
    performanceImpliesEndorsementIsFalse :
      performanceImpliesEndorsement ≡ false

canonicalPowersPlantationParadiseBoundary : PowersPlantationParadiseBoundary
canonicalPowersPlantationParadiseBoundary =
  powers-plantation-paradise-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
