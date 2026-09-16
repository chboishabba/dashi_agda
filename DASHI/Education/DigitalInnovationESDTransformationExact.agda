module DASHI.Education.DigitalInnovationESDTransformationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as Intersection

data TransformationCoordinate : Set where
  pedagogyCoordinate : TransformationCoordinate
  curriculumCoordinate : TransformationCoordinate
  learningEnvironmentCoordinate : TransformationCoordinate
  competenceCoordinate : TransformationCoordinate
  institutionalPracticeCoordinate : TransformationCoordinate

data SustainabilityCoordinate : Set where
  environmentalChallengeCoordinate : SustainabilityCoordinate
  socialChallengeCoordinate : SustainabilityCoordinate
  economicChallengeCoordinate : SustainabilityCoordinate

data ScalingCondition : Set where
  scalablePedagogyCondition : ScalingCondition
  institutionalPracticeCondition : ScalingCondition
  professionalDevelopmentCondition : ScalingCondition
  policyCondition : ScalingCondition

record TwinTransitionCoordinates : Set where
  constructor twinTransitionCoordinates
  field
    transformedEducation : List TransformationCoordinate
    sustainabilityAgenda : List SustainabilityCoordinate
    scalingConditions : List ScalingCondition
    integrationReference : String

canonicalTwinTransitionCoordinates : TwinTransitionCoordinates
canonicalTwinTransitionCoordinates =
  twinTransitionCoordinates
    (pedagogyCoordinate ∷ curriculumCoordinate ∷ learningEnvironmentCoordinate
      ∷ competenceCoordinate ∷ institutionalPracticeCoordinate ∷ [])
    (environmentalChallengeCoordinate ∷ socialChallengeCoordinate
      ∷ economicChallengeCoordinate ∷ [])
    (scalablePedagogyCondition ∷ institutionalPracticeCondition
      ∷ professionalDevelopmentCondition ∷ policyCondition ∷ [])
    "digital transformation and ESD are joined through changed educational structures plus explicit scaling conditions"

data Intervention : Set where
  parallelAgendaDeployment : Intervention
  integratedTwinTransitionDeployment : Intervention

data TechnologyUse : Set where
  digitallyEnhancedPlatform : TechnologyUse

technologyUse : Intervention → TechnologyUse
technologyUse parallelAgendaDeployment = digitallyEnhancedPlatform
technologyUse integratedTwinTransitionDeployment = digitallyEnhancedPlatform

transformativeESDOutcome : Intervention → Bool
transformativeESDOutcome parallelAgendaDeployment = false
transformativeESDOutcome integratedTwinTransitionDeployment = true

technologyUseCollision :
  Intersection.NonFactorabilityWitness technologyUse transformativeESDOutcome
technologyUseCollision =
  Intersection.nonFactorabilityWitness
    parallelAgendaDeployment
    integratedTwinTransitionDeployment
    refl
    (λ ())

technologyUseCannotDetermineTransformativeESD :
  Intersection.FactorsThrough technologyUse transformativeESDOutcome → ⊥
technologyUseCannotDetermineTransformativeESD =
  Intersection.witnessRulesOutEveryFlatFactorisation technologyUseCollision

data LearningGain : Set where
  measuredLearningGain : LearningGain

learningGain : Intervention → LearningGain
learningGain parallelAgendaDeployment = measuredLearningGain
learningGain integratedTwinTransitionDeployment = measuredLearningGain

systemResponseCapacity : Intervention → Bool
systemResponseCapacity parallelAgendaDeployment = false
systemResponseCapacity integratedTwinTransitionDeployment = true

learningGainCollision :
  Intersection.NonFactorabilityWitness learningGain systemResponseCapacity
learningGainCollision =
  Intersection.nonFactorabilityWitness
    parallelAgendaDeployment
    integratedTwinTransitionDeployment
    refl
    (λ ())

learningGainCannotDetermineSystemResponseCapacity :
  Intersection.FactorsThrough learningGain systemResponseCapacity → ⊥
learningGainCannotDetermineSystemResponseCapacity =
  Intersection.witnessRulesOutEveryFlatFactorisation learningGainCollision

data SeparateAgendasAutoIntegratePermission : Set where

separateAgendasCannotAutoPromoteToIntegratedTransition :
  SeparateAgendasAutoIntegratePermission → ⊥
separateAgendasCannotAutoPromoteToIntegratedTransition ()

record IntegratedTransitionBoundary : Set where
  constructor integratedTransitionBoundary
  field
    technologyUseEqualsEducationalTransformation : Bool
    technologyUseEqualsEducationalTransformationIsFalse :
      technologyUseEqualsEducationalTransformation ≡ false
    learningGainEqualsSystemResponseCapacity : Bool
    learningGainEqualsSystemResponseCapacityIsFalse :
      learningGainEqualsSystemResponseCapacity ≡ false
    separateAgendaLabelsSupplyIntegration : Bool
    separateAgendaLabelsSupplyIntegrationIsFalse :
      separateAgendaLabelsSupplyIntegration ≡ false
    pedagogyInstitutionProfessionAndPolicyRemainRetained : Bool
    pedagogyInstitutionProfessionAndPolicyRemainRetainedIsTrue :
      pedagogyInstitutionProfessionAndPolicyRemainRetained ≡ true

canonicalIntegratedTransitionBoundary : IntegratedTransitionBoundary
canonicalIntegratedTransitionBoundary =
  integratedTransitionBoundary false refl false refl false refl true refl
