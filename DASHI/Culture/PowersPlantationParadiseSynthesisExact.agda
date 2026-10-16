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
import DASHI.Culture.PowersPlantationParadiseHistoricalClaimReceiptsExact as Claims
import DASHI.Culture.ColonialPerformanceStatusNonfactorabilityExact as Performance
import DASHI.Culture.HistoricalArchiveAbsenceNonfactorabilityExact as Archive
import DASHI.Culture.ColonialTheatreAccessAdapterExact as Access
import DASHI.Culture.PowersPlantationParadiseGovernedCrossPollinationExact as GovernedCross
import DASHI.Culture.PowersPlantationParadiseEmpiricalProgrammeExact as Empirical
import DASHI.Culture.PowersPlantationParadiseEmpiricalAcquisitionParetoExact as EmpiricalPareto
import DASHI.Culture.PowersPlantationParadisePerformerComparisonExact as PerformerComparison
import DASHI.Culture.PowersPlantationParadiseComparativeVenueEvidenceExact as ComparativeVenue
import DASHI.Culture.PowersPlantationParadiseEnslavedDistributionEvidenceExact as EnslavedEvidence
import DASHI.Culture.PowersPlantationParadiseMethodologySourceAtlasExact as Methodology
import DASHI.Culture.PowersPlantationParadiseArchiveModalityExact as ArchiveModality
import DASHI.Culture.PowersPlantationParadiseInvestigationParetoExact as InvestigationRouting
import DASHI.Culture.PowersPlantationParadiseHistoricalDiscriminatorExact as Discriminator
import DASHI.Culture.ColonialTheatreSensoryAccessExact as Sensory
import DASHI.Culture.PowersPlantationParadiseEvidenceGraphExact as EvidenceGraph
import DASHI.Culture.PowersPlantationParadiseMobilityRegimeTransitionExact as Mobility
import DASHI.Culture.PowersPlantationParadiseResearchThroughPerformanceExact as PerformanceProbe
import DASHI.Culture.PowersPlantationParadiseEmpiricalRoadmapExact as Roadmap

------------------------------------------------------------------------
-- POWERS PLANTATION -> PARADISE? SYNTHESIS
------------------------------------------------------------------------

data PowersHistoricalState : Set where
  paradiseSurfaceRestrictedMaterial : PowersHistoricalState
  paradiseSurfaceExpandedMaterial : PowersHistoricalState

data ParadiseObserverReading : Set where paradiseSurface : ParadiseObserverReading
data MaterialAffordance : Set where materiallyRestricted materiallyExpanded : MaterialAffordance

paradiseObserver : PowersHistoricalState → ParadiseObserverReading
paradiseObserver _ = paradiseSurface

materialAffordance : PowersHistoricalState → MaterialAffordance
materialAffordance paradiseSurfaceRestrictedMaterial = materiallyRestricted
materialAffordance paradiseSurfaceExpandedMaterial = materiallyExpanded

materialAffordanceDiffers :
  materialAffordance paradiseSurfaceRestrictedMaterial ≡ materialAffordance paradiseSurfaceExpandedMaterial → ⊥
materialAffordanceDiffers ()

paradiseObserverCannotRecoverMaterialAffordance :
  INF.FactorsThrough paradiseObserver materialAffordance → ⊥
paradiseObserverCannotRecoverMaterialAffordance =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness paradiseSurfaceRestrictedMaterial paradiseSurfaceExpandedMaterial refl materialAffordanceDiffers)

existingObserverAffordanceDonor :
  INF.FactorsThrough Ecology.nominalLiberatoryObserver Ecology.realizedRemain → ⊥
existingObserverAffordanceDonor = Ecology.nominalLiberatoryLabelCannotRecoverRealizedAffordance

recognitionCannotRecoverDistribution : INF.FactorsThrough Fraser.recognition Fraser.distribution → ⊥
recognitionCannotRecoverDistribution = Fraser.recognitionCannotRecoverDistribution

distributionCannotRecoverRepresentation : INF.FactorsThrough Fraser.distribution Fraser.representation → ⊥
distributionCannotRecoverRepresentation = Fraser.distributionCannotRecoverRepresentation

data ExpansionState : Set where localExpandedGloballyRestricted localExpandedGloballyOpen : ExpansionState
data LocalExpansion : Set where localOptionExpanded : LocalExpansion
data GlobalEmancipation : Set where globalRestrictionRemains globalRestrictionRemoved : GlobalEmancipation

localExpansion : ExpansionState → LocalExpansion
localExpansion _ = localOptionExpanded

globalEmancipation : ExpansionState → GlobalEmancipation
globalEmancipation localExpandedGloballyRestricted = globalRestrictionRemains
globalEmancipation localExpandedGloballyOpen = globalRestrictionRemoved

globalEmancipationDiffers :
  globalEmancipation localExpandedGloballyRestricted ≡ globalEmancipation localExpandedGloballyOpen → ⊥
globalEmancipationDiffers ()

localExpansionDoesNotProveGlobalEmancipation : INF.FactorsThrough localExpansion globalEmancipation → ⊥
localExpansionDoesNotProveGlobalEmancipation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness localExpandedGloballyRestricted localExpandedGloballyOpen refl globalEmancipationDiffers)

data EpistemicLayer : Set where powersSourceClaim dashiTheorem : EpistemicLayer

sourceClaimDoesNotBecomeDASHITheorem : powersSourceClaim ≡ dashiTheorem → ⊥
sourceClaimDoesNotBecomeDASHITheorem ()

sourceBoundary : Sources.PowersSourceBoundary
sourceBoundary = Sources.canonicalPowersSourceBoundary

historicalClaimBoundary : Claims.PowersHistoricalClaimBoundary
historicalClaimBoundary = Claims.canonicalPowersHistoricalClaimBoundary

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

governedCrossPollinationBoundary : GovernedCross.PowersGovernedCrossPollinationBoundary
governedCrossPollinationBoundary = GovernedCross.canonicalPowersGovernedCrossPollinationBoundary

empiricalProgrammeBoundary : Empirical.PowersEmpiricalProgrammeBoundary
empiricalProgrammeBoundary = Empirical.canonicalPowersEmpiricalProgrammeBoundary

empiricalAcquisitionParetoBoundary : EmpiricalPareto.PowersEmpiricalAcquisitionParetoBoundary
empiricalAcquisitionParetoBoundary = EmpiricalPareto.canonicalPowersEmpiricalAcquisitionParetoBoundary

performerComparisonBoundary : PerformerComparison.PowersPerformerComparisonBoundary
performerComparisonBoundary = PerformerComparison.canonicalPowersPerformerComparisonBoundary

comparativeVenueEvidenceBoundary : ComparativeVenue.PowersComparativeVenueEvidenceBoundary
comparativeVenueEvidenceBoundary = ComparativeVenue.canonicalPowersComparativeVenueEvidenceBoundary

enslavedDistributionEvidenceBoundary : EnslavedEvidence.PowersEnslavedDistributionEvidenceBoundary
enslavedDistributionEvidenceBoundary = EnslavedEvidence.canonicalPowersEnslavedDistributionEvidenceBoundary

methodologySourceBoundary : Methodology.PowersMethodologySourceBoundary
methodologySourceBoundary = Methodology.canonicalPowersMethodologySourceBoundary

archiveModalityBoundary : ArchiveModality.PowersArchiveModalityBoundary
archiveModalityBoundary = ArchiveModality.canonicalPowersArchiveModalityBoundary

investigationRoutingBoundary : InvestigationRouting.PowersInvestigationRoutingBoundary
investigationRoutingBoundary = InvestigationRouting.canonicalPowersInvestigationRoutingBoundary

historicalDiscriminatorBoundary : Discriminator.PowersHistoricalDiscriminatorBoundary
historicalDiscriminatorBoundary = Discriminator.canonicalPowersHistoricalDiscriminatorBoundary

sensoryAccessBoundary : Sensory.ColonialTheatreSensoryAccessBoundary
sensoryAccessBoundary = Sensory.canonicalColonialTheatreSensoryAccessBoundary

evidenceGraphBoundary : EvidenceGraph.PowersEvidenceGraphBoundary
evidenceGraphBoundary = EvidenceGraph.canonicalPowersEvidenceGraphBoundary

mobilityRegimeBoundary : Mobility.PowersMobilityRegimeBoundary
mobilityRegimeBoundary = Mobility.canonicalPowersMobilityRegimeBoundary

researchThroughPerformanceBoundary : PerformanceProbe.PowersResearchThroughPerformanceBoundary
researchThroughPerformanceBoundary = PerformanceProbe.canonicalPowersResearchThroughPerformanceBoundary

empiricalRoadmapBoundary : Roadmap.PowersEmpiricalRoadmapBoundary
empiricalRoadmapBoundary = Roadmap.canonicalPowersEmpiricalRoadmapBoundary

record PowersPlantationParadiseBoundary : Set where
  constructor powers-plantation-paradise-boundary
  field
    paradiseProjectionEqualsHistoricalCarrier : Bool
    paradiseProjectionEqualsHistoricalCarrierIsFalse : paradiseProjectionEqualsHistoricalCarrier ≡ false
    culturalVisibilityImpliesMaterialFreedom : Bool
    culturalVisibilityImpliesMaterialFreedomIsFalse : culturalVisibilityImpliesMaterialFreedom ≡ false
    localOptionExpansionImpliesGlobalEmancipation : Bool
    localOptionExpansionImpliesGlobalEmancipationIsFalse : localOptionExpansionImpliesGlobalEmancipation ≡ false
    archiveSilenceImpliesHistoricalAbsence : Bool
    archiveSilenceImpliesHistoricalAbsenceIsFalse : archiveSilenceImpliesHistoricalAbsence ≡ false
    performanceImpliesSocialOccupancy : Bool
    performanceImpliesSocialOccupancyIsFalse : performanceImpliesSocialOccupancy ≡ false
    performanceImpliesEndorsement : Bool
    performanceImpliesEndorsementIsFalse : performanceImpliesEndorsement ≡ false
    culturalSurfaceImpliesSameStanding : Bool
    culturalSurfaceImpliesSameStandingIsFalse : culturalSurfaceImpliesSameStanding ≡ false
    culturalSurfaceImpliesPoliticalContestability : Bool
    culturalSurfaceImpliesPoliticalContestabilityIsFalse : culturalSurfaceImpliesPoliticalContestability ≡ false
    culturalSurfaceImpliesSameMaterialCone : Bool
    culturalSurfaceImpliesSameMaterialConeIsFalse : culturalSurfaceImpliesSameMaterialCone ≡ false

canonicalPowersPlantationParadiseBoundary : PowersPlantationParadiseBoundary
canonicalPowersPlantationParadiseBoundary =
  powers-plantation-paradise-boundary
    false refl false refl false refl false refl false refl false refl false refl false refl false refl
