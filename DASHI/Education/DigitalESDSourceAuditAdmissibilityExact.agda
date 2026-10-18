module DASHI.Education.DigitalESDSourceAuditAdmissibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDNormativeStandardsAtlasExact as Standards
import DASHI.Education.DigitalESDSituatedAuditObserverExact as Observer

------------------------------------------------------------------------
-- QUERY-RELATIVE ADMISSIBILITY
------------------------------------------------------------------------

data AuditConsumerQuestion : Set where
  aiGovernanceRequirement : AuditConsumerQuestion
  studentLearningEffect : AuditConsumerQuestion
  livedAccessibilityExperience : AuditConsumerQuestion
  nationalPrevalence : AuditConsumerQuestion
  reportedFabricationWaterUse : AuditConsumerQuestion
  specificSchoolAIWaterFootprint : AuditConsumerQuestion
  participantDecisionAuthority : AuditConsumerQuestion
  materialLifecycleBurden : AuditConsumerQuestion

data AdmissibilityStatus : Set where
  admissible : AdmissibilityStatus
  inadmissibleWrongConsumer : AdmissibilityStatus
  unresolvedAdmissibility : AdmissibilityStatus

record AdmissibleEvidenceFibre : Set where
  constructor admissible-evidence-fibre
  field
    observation : Observer.SituatedAuditObservation
    question : AuditConsumerQuestion
    status : AdmissibilityStatus
    reason : String
    preservesClaimCeiling : Bool
    preservesClaimCeilingIsTrue : preservesClaimCeiling ≡ true

open AdmissibleEvidenceFibre public

standardLensAdmissibility : Standards.StandardLens → AuditConsumerQuestion → AdmissibilityStatus
standardLensAdmissibility _ aiGovernanceRequirement = admissible
standardLensAdmissibility _ studentLearningEffect = inadmissibleWrongConsumer
standardLensAdmissibility _ livedAccessibilityExperience = unresolvedAdmissibility
standardLensAdmissibility _ nationalPrevalence = inadmissibleWrongConsumer
standardLensAdmissibility _ reportedFabricationWaterUse = inadmissibleWrongConsumer
standardLensAdmissibility _ specificSchoolAIWaterFootprint = inadmissibleWrongConsumer
standardLensAdmissibility _ participantDecisionAuthority = unresolvedAdmissibility
standardLensAdmissibility _ materialLifecycleBurden = unresolvedAdmissibility

------------------------------------------------------------------------
-- WrongType / no-promotion family.
------------------------------------------------------------------------

data ScoreProjectionCreatesSourceQuality : Set where
data StandardSatisfiedCreatesObservedOutcome : Set where
data ParticipantPresenceCreatesAuthority : Set where
data AccessProvidedCreatesEffectiveAccessibility : Set where
data AIGovernanceCreatesAISafety : Set where
data SecurityAvailabilityCreatesHumanAccessibility : Set where
data EnvironmentalEfficiencyCreatesEnvironmentalSustainability : Set where
data MarketEfficiencyCreatesDistributiveJustice : Set where
data OpenSourceCreatesCommonsGovernance : Set where
data IndigenousCitationCreatesIndigenousAuthority : Set where
data SharedConclusionCreatesSharedEpistemology : Set where

scoreProjectionDoesNotCreateSourceQuality : ScoreProjectionCreatesSourceQuality → ⊥
scoreProjectionDoesNotCreateSourceQuality ()

standardSatisfiedDoesNotCreateObservedOutcome : StandardSatisfiedCreatesObservedOutcome → ⊥
standardSatisfiedDoesNotCreateObservedOutcome ()

participantPresenceDoesNotCreateAuthority : ParticipantPresenceCreatesAuthority → ⊥
participantPresenceDoesNotCreateAuthority ()

accessProvidedDoesNotCreateEffectiveAccessibility :
  AccessProvidedCreatesEffectiveAccessibility → ⊥
accessProvidedDoesNotCreateEffectiveAccessibility ()

aiGovernanceDoesNotCreateAISafety : AIGovernanceCreatesAISafety → ⊥
aiGovernanceDoesNotCreateAISafety ()

securityAvailabilityDoesNotCreateHumanAccessibility :
  SecurityAvailabilityCreatesHumanAccessibility → ⊥
securityAvailabilityDoesNotCreateHumanAccessibility ()

environmentalEfficiencyDoesNotCreateEnvironmentalSustainability :
  EnvironmentalEfficiencyCreatesEnvironmentalSustainability → ⊥
environmentalEfficiencyDoesNotCreateEnvironmentalSustainability ()

marketEfficiencyDoesNotCreateDistributiveJustice :
  MarketEfficiencyCreatesDistributiveJustice → ⊥
marketEfficiencyDoesNotCreateDistributiveJustice ()

openSourceDoesNotCreateCommonsGovernance : OpenSourceCreatesCommonsGovernance → ⊥
openSourceDoesNotCreateCommonsGovernance ()

indigenousCitationDoesNotCreateIndigenousAuthority :
  IndigenousCitationCreatesIndigenousAuthority → ⊥
indigenousCitationDoesNotCreateIndigenousAuthority ()

sharedConclusionDoesNotCreateSharedEpistemology :
  SharedConclusionCreatesSharedEpistemology → ⊥
sharedConclusionDoesNotCreateSharedEpistemology ()

record AuditAdmissibilityBoundary : Set where
  constructor audit-admissibility-boundary
  field
    admissibilityIsConsumerRelative : Bool
    admissibilityIsConsumerRelativeIsTrue : admissibilityIsConsumerRelative ≡ true
    admissibilityRaisesClaimCeiling : Bool
    admissibilityRaisesClaimCeilingIsFalse : admissibilityRaisesClaimCeiling ≡ false
    standardLensUniversallyAdmissible : Bool
    standardLensUniversallyAdmissibleIsFalse : standardLensUniversallyAdmissible ≡ false

open AuditAdmissibilityBoundary public

canonicalAuditAdmissibilityBoundary : AuditAdmissibilityBoundary
canonicalAuditAdmissibilityBoundary = audit-admissibility-boundary
  true refl
  false refl
  false refl
