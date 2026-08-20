module DASHI.Education.EarlyLearningComparativeArchitectureExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Education.EarlyLearningIntersectionalCapabilityExact as Capability

------------------------------------------------------------------------
-- COMPARATIVE DELIVERY ARCHITECTURE
--
-- Professional entitlement, actual delivery quality, pedagogical structure,
-- rollout pace, workforce capacity and the counterfactual home environment are
-- separate coordinates.  Hence neither "professional floor retained" nor
-- "home delivery" is a sufficient outcome carrier.
------------------------------------------------------------------------

data DeliverySite : Set where
  centreDelivery homeDelivery hybridDelivery : DeliverySite

data ProfessionalRelation : Set where
  noQualifiedRelation periodicQualifiedRelation continuousQualifiedRelation : ProfessionalRelation

data PedagogicalStructure : Set where
  lowExplicitStructure guidedFlexibleStructure formalStructuredProgramme : PedagogicalStructure

data QualityState : Set where
  qualityUnknown qualityConstrained highQualityCapacity : QualityState

data RolloutState : Set where
  rapidScaleUp matureCapacityBuild : RolloutState

data CounterfactualHomeState : Set where
  lowerOpportunityCounterfactual higherOpportunityCounterfactual : CounterfactualHomeState

data LabourEffectRisk : Set where
  labourEffectUnknown maternalExitRisk labourParticipationGain : LabourEffectRisk

data AutonomyState : Set where
  lowAutonomy developmentallyAppropriateAutonomy highUnstructuredAutonomy : AutonomyState

record ComparativeLearningArchitecture : Set where
  constructor comparativeLearningArchitecture
  field
    deliverySite : DeliverySite
    professionalRelation : ProfessionalRelation
    structure : PedagogicalStructure
    quality : QualityState
    rollout : RolloutState
    counterfactualHome : CounterfactualHomeState
    labourEffect : LabourEffectRisk
    autonomy : AutonomyState
    childEntitlementRetained : Bool
    contextualReviewAvailable : Bool
    architectureLabel : String

open ComparativeLearningArchitecture public

quebecRapidUniversalWitness : ComparativeLearningArchitecture
quebecRapidUniversalWitness =
  comparativeLearningArchitecture centreDelivery continuousQualifiedRelation
    formalStructuredProgramme qualityConstrained rapidScaleUp
    higherOpportunityCounterfactual labourParticipationGain lowAutonomy
    true false
    "finite structural witness inspired by Quebec: public entitlement can coexist with rollout/quality/counterfactual coordinates that remain outcome-relevant"

matureHighQualityUniversalWitness : ComparativeLearningArchitecture
matureHighQualityUniversalWitness =
  comparativeLearningArchitecture centreDelivery continuousQualifiedRelation
    formalStructuredProgramme highQualityCapacity matureCapacityBuild
    lowerOpportunityCounterfactual labourParticipationGain developmentallyAppropriateAutonomy
    true true
    "finite contrasting witness: same professional-entitlement label, different quality/rollout/counterfactual coordinates"

professionalFloorProjection : ComparativeLearningArchitecture → Bool
professionalFloorProjection architecture = childEntitlementRetained architecture

comparativeOutcomeWitness : ComparativeLearningArchitecture → Bool
comparativeOutcomeWitness quebecRapidUniversalWitness = false
comparativeOutcomeWitness matureHighQualityUniversalWitness = true
comparativeOutcomeWitness architecture = false

sameProfessionalFloorDifferentOutcome :
  comparativeOutcomeWitness quebecRapidUniversalWitness ≡
  comparativeOutcomeWitness matureHighQualityUniversalWitness → ⊥
sameProfessionalFloorDifferentOutcome ()

professionalFloorNonFactorability :
  Intersection.NonFactorabilityWitness
    professionalFloorProjection comparativeOutcomeWitness
professionalFloorNonFactorability =
  Intersection.nonFactorabilityWitness
    quebecRapidUniversalWitness matureHighQualityUniversalWitness refl
    sameProfessionalFloorDifferentOutcome

professionalFloorCannotDetermineOutcome :
  Intersection.FactorsThrough
    professionalFloorProjection comparativeOutcomeWitness → ⊥
professionalFloorCannotDetermineOutcome =
  Intersection.witnessRulesOutEveryFlatFactorisation
    professionalFloorNonFactorability

------------------------------------------------------------------------
-- Home delivery also fails as a sufficient carrier because structure and
-- qualified relational support remain independent coordinates.
------------------------------------------------------------------------

structuredHomeWitness : ComparativeLearningArchitecture
structuredHomeWitness =
  comparativeLearningArchitecture homeDelivery periodicQualifiedRelation
    formalStructuredProgramme highQualityCapacity matureCapacityBuild
    higherOpportunityCounterfactual labourEffectUnknown developmentallyAppropriateAutonomy
    true true
    "structured home-learning witness with retained public/professional relation"

unstructuredHomeWitness : ComparativeLearningArchitecture
unstructuredHomeWitness =
  comparativeLearningArchitecture homeDelivery noQualifiedRelation
    lowExplicitStructure qualityUnknown matureCapacityBuild
    higherOpportunityCounterfactual labourEffectUnknown highUnstructuredAutonomy
    false false
    "unstructured home-learning witness"

homeProjection : ComparativeLearningArchitecture → Bool
homeProjection structuredHomeWitness = true
homeProjection unstructuredHomeWitness = true
homeProjection architecture = false

homeAcademicWitness : ComparativeLearningArchitecture → Bool
homeAcademicWitness structuredHomeWitness = true
homeAcademicWitness unstructuredHomeWitness = false
homeAcademicWitness architecture = false

sameHomeDifferentAcademicWitness :
  homeAcademicWitness structuredHomeWitness ≡ homeAcademicWitness unstructuredHomeWitness → ⊥
sameHomeDifferentAcademicWitness ()

homeDeliveryNonFactorability :
  Intersection.NonFactorabilityWitness homeProjection homeAcademicWitness
homeDeliveryNonFactorability =
  Intersection.nonFactorabilityWitness
    structuredHomeWitness unstructuredHomeWitness refl
    sameHomeDifferentAcademicWitness

homeDeliveryCannotDetermineAcademicOutcome :
  Intersection.FactorsThrough homeProjection homeAcademicWitness → ⊥
homeDeliveryCannotDetermineAcademicOutcome =
  Intersection.witnessRulesOutEveryFlatFactorisation homeDeliveryNonFactorability

------------------------------------------------------------------------
-- Counter-case discipline: institutional authority is not always protective,
-- and parental autonomy is not always a risk.  Direction must be supplied by
-- domain-specific evidence rather than the actor label alone.
------------------------------------------------------------------------

data InstitutionalAlwaysProtectivePermission : Set where
data ParentalAutonomyAlwaysRiskPermission : Set where

institutionalAuthorityCannotAutoPromoteToProtection :
  InstitutionalAlwaysProtectivePermission → ⊥
institutionalAuthorityCannotAutoPromoteToProtection ()

parentalAutonomyCannotAutoPromoteToRisk :
  ParentalAutonomyAlwaysRiskPermission → ⊥
parentalAutonomyCannotAutoPromoteToRisk ()

------------------------------------------------------------------------
-- Reuse situated capability: policy effect depends on what the intervention
-- changes relative to the family's actual starting topology/counterfactual.
------------------------------------------------------------------------

situatedCapabilityStillPrimary :
  Intersection.FactorsThrough
    Capability.familyChoiceProjection Capability.effectiveCapabilityWitness → ⊥
situatedCapabilityStillPrimary = Capability.familyChoiceCannotDetermineEffectiveCapability

comparativeArchitectureReading : String
comparativeArchitectureReading =
  "Quebec, Nordic cash-for-care, structured homeschooling, unstructured homeschooling, Waldorf-inspired schools and autonomy-oriented parenting cannot be ranked by a home-versus-institution scalar. Professional entitlement, quality, pedagogical structure, rollout/workforce capacity, counterfactual home environment, labour effects and developmentally appropriate autonomy remain distinct coordinates."
