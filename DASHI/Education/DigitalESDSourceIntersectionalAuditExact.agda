module DASHI.Education.DigitalESDSourceIntersectionalAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Education.DigitalESDSourceAuditScaleExact as Scale
import DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact as Disability
import DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact as Absence
import DASHI.Education.DigitalESDExternalityIncidenceAuditExact as Incidence
import DASHI.Education.DigitalESDPoliticalEconomyProvisioningExact as PoliticalEconomy
import DASHI.Education.DigitalESDSocialProvisioningContinuityExact as Provisioning
import DASHI.Education.DigitalESDInstitutionalDurabilityMaintenanceExact as Durability

------------------------------------------------------------------------
-- SPARSE INTERSECTION FIBRES
------------------------------------------------------------------------

data IntersectionFamily : Set where
  disabilityAccessByAffordability : IntersectionFamily
  disabilityAccessByMaintenanceDurability : IntersectionFamily
  disabilityAccessBySocialProvisioning : IntersectionFamily
  representationByParticipantAuthority : IntersectionFamily
  politicalEconomyByExternalityIncidence : IntersectionFamily
  politicalEconomyByMaterialLifecycle : IntersectionFamily
  politicalEconomyByLabourMaintenance : IntersectionFamily
  environmentalBurdenByPlaceCommunity : IntersectionFamily
  presentBenefitByFutureIntergenerationalBurden : IntersectionFamily
  deliveryModeByHouseholdCareProvisioning : IntersectionFamily
  vendorDependenceByPracticalExitAccessibility : IntersectionFamily
  disabilityAccessByInteractionUsability : IntersectionFamily
  disabilityAccessByPrivacyDisclosure : IntersectionFamily
  participantAuthorityByDataGovernancePrivacy : IntersectionFamily
  aiGovernanceByParticipantAuthority : IntersectionFamily
  aiRiskByExternalityIncidence : IntersectionFamily
  securityAvailabilityByPracticalAccessibility : IntersectionFamily
  serviceContinuityByDisabilitySupportContinuity : IntersectionFamily
  serviceManagementByMaintenanceLabourFunding : IntersectionFamily
  qualityImprovementByParticipantDefinedOutcomes : IntersectionFamily
  processEfficiencyByAbsoluteEnvironmentalThroughput : IntersectionFamily
  humanCentredDesignByRepresentedDesignPopulation : IntersectionFamily
  physicalSpaceAccessibilityByOnlineDeliverySubstitution : IntersectionFamily
  privacySecurityByPracticalExitDataPortability : IntersectionFamily

canonicalIntersectionFamilies : List IntersectionFamily
canonicalIntersectionFamilies =
  disabilityAccessByAffordability
  ∷ disabilityAccessByMaintenanceDurability
  ∷ disabilityAccessBySocialProvisioning
  ∷ representationByParticipantAuthority
  ∷ politicalEconomyByExternalityIncidence
  ∷ politicalEconomyByMaterialLifecycle
  ∷ politicalEconomyByLabourMaintenance
  ∷ environmentalBurdenByPlaceCommunity
  ∷ presentBenefitByFutureIntergenerationalBurden
  ∷ deliveryModeByHouseholdCareProvisioning
  ∷ vendorDependenceByPracticalExitAccessibility
  ∷ disabilityAccessByInteractionUsability
  ∷ disabilityAccessByPrivacyDisclosure
  ∷ participantAuthorityByDataGovernancePrivacy
  ∷ aiGovernanceByParticipantAuthority
  ∷ aiRiskByExternalityIncidence
  ∷ securityAvailabilityByPracticalAccessibility
  ∷ serviceContinuityByDisabilitySupportContinuity
  ∷ serviceManagementByMaintenanceLabourFunding
  ∷ qualityImprovementByParticipantDefinedOutcomes
  ∷ processEfficiencyByAbsoluteEnvironmentalThroughput
  ∷ humanCentredDesignByRepresentedDesignPopulation
  ∷ physicalSpaceAccessibilityByOnlineDeliverySubstitution
  ∷ privacySecurityByPracticalExitDataPortability
  ∷ []

record IntersectionReceipt : Set where
  constructor intersection-receipt
  field
    source : Attr.AttributedSource
    family : IntersectionFamily
    leftComponentScore : Scale.Score0to5
    rightComponentScore : Scale.Score0to5
    interactionScore : Scale.Score0to5
    reason : String
    supportingLocator : String
    limitation : String

open IntersectionReceipt public

------------------------------------------------------------------------
-- Canonical donor boundaries: this owner composes them but does not replace
-- their source atlases or empirical authority surfaces.
------------------------------------------------------------------------

disabilityBoundary : Disability.DisabilityDigitalESDBoundary
disabilityBoundary = Disability.canonicalDisabilityDigitalESDBoundary

absenceQuestionCount = Absence.absenceAuditQuestionCount

incidenceBoundary : Incidence.ExternalityIncidenceBoundary
incidenceBoundary = Incidence.canonicalExternalityIncidenceBoundary

politicalEconomyBoundary : PoliticalEconomy.DigitalESDPoliticalEconomyBoundary
politicalEconomyBoundary = PoliticalEconomy.canonicalDigitalESDPoliticalEconomyBoundary

socialProvisioningBoundary : Provisioning.SocialProvisioningBoundary
socialProvisioningBoundary = Provisioning.canonicalSocialProvisioningBoundary

durabilityBoundary : Durability.InstitutionalDurabilityBoundary
durabilityBoundary = Durability.canonicalInstitutionalDurabilityBoundary

------------------------------------------------------------------------
-- Same component scores, different interaction coverage.
------------------------------------------------------------------------

data IntersectionWorld : Set where
  componentStrongInteractionAbsent : IntersectionWorld
  componentStrongInteractionDirect : IntersectionWorld

ComponentScoreSurface : Set
ComponentScoreSurface = Scale.Score0to5 × Scale.Score0to5

componentScoreProjection : IntersectionWorld → ComponentScoreSurface
componentScoreProjection componentStrongInteractionAbsent =
  Scale.score4Substantial , Scale.score4Substantial
componentScoreProjection componentStrongInteractionDirect =
  Scale.score4Substantial , Scale.score4Substantial

interactionCoverage : IntersectionWorld → Scale.Score0to5
interactionCoverage componentStrongInteractionAbsent = Scale.score0Absent
interactionCoverage componentStrongInteractionDirect = Scale.score3DirectIncomplete

interactionCoverageDiffers :
  interactionCoverage componentStrongInteractionAbsent ≡
  interactionCoverage componentStrongInteractionDirect → ⊥
interactionCoverageDiffers ()

componentScoresIntersectionWitness :
  INF.NonFactorabilityWitness componentScoreProjection interactionCoverage
componentScoresIntersectionWitness =
  INF.nonFactorabilityWitness
    componentStrongInteractionAbsent
    componentStrongInteractionDirect
    refl
    interactionCoverageDiffers

componentScoreProjectionCannotDetermineIntersectionCoverage :
  INF.FactorsThrough componentScoreProjection interactionCoverage → ⊥
componentScoreProjectionCannotDetermineIntersectionCoverage =
  INF.witnessRulesOutEveryFlatFactorisation componentScoresIntersectionWitness

data ComponentScoresDetermineIntersectionCoverage : Set where

componentScoresDoNotDetermineIntersectionCoverage :
  ComponentScoresDetermineIntersectionCoverage → ⊥
componentScoresDoNotDetermineIntersectionCoverage ()

intersectionReading : String
intersectionReading =
  "Intersectionality is represented by consumer-relevant joint fibres, not by adding marginal scores. A source may substantially cover disability/access and affordability separately while never observing how affordability changes disability-specific access; the interaction therefore remains independently auditable."
