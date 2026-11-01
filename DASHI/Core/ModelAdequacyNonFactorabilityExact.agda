module DASHI.Core.ModelAdequacyNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- MODEL ADEQUACY AS CONSUMER-RELATIVE FACTORABILITY
--
-- DASHI-original generic mathematics, reusing the repository's established
-- NonFactorabilityWitness compiler.
------------------------------------------------------------------------

record ModelAdequacyProblem : Set₁ where
  constructor model-adequacy-problem
  field
    World ModelObservation ConsumerOutcome : Set
    observeModel : World → ModelObservation
    targetForConsumer : World → ConsumerOutcome

open ModelAdequacyProblem public

ModelAdequateFor : ModelAdequacyProblem → Set₁
ModelAdequateFor problem =
  INF.FactorsThrough (observeModel problem) (targetForConsumer problem)

record ModelInadequacyWitness (problem : ModelAdequacyProblem) : Set₁ where
  constructor model-inadequacy-witness
  field
    witness :
      INF.NonFactorabilityWitness
        (observeModel problem)
        (targetForConsumer problem)

open ModelInadequacyWitness public

inadequacyWitnessRulesOutAdequacy :
  ∀ {problem} →
  ModelInadequacyWitness problem →
  ModelAdequateFor problem →
  ⊥
inadequacyWitnessRulesOutAdequacy receipt =
  INF.witnessRulesOutEveryFlatFactorisation (witness receipt)

------------------------------------------------------------------------
-- Exact finite fixture: the same model observation can be sufficient for one
-- consumer and structurally insufficient for another.
------------------------------------------------------------------------

data FixtureWorld : Set where
  lowHydrology : FixtureWorld
  highHydrology : FixtureWorld

data EconomicObservation : Set where
  sameAvoidedCost : EconomicObservation

data EconomicOutcome : Set where
  sameEconomicOutcome : EconomicOutcome

data EcologicalOutcome : Set where
  lowEcologicalResponse : EcologicalOutcome
  highEcologicalResponse : EcologicalOutcome

economicObservation : FixtureWorld → EconomicObservation
economicObservation lowHydrology = sameAvoidedCost
economicObservation highHydrology = sameAvoidedCost

economicOutcome : FixtureWorld → EconomicOutcome
economicOutcome lowHydrology = sameEconomicOutcome
economicOutcome highHydrology = sameEconomicOutcome

ecologicalOutcome : FixtureWorld → EcologicalOutcome
ecologicalOutcome lowHydrology = lowEcologicalResponse
ecologicalOutcome highHydrology = highEcologicalResponse

economicProblem : ModelAdequacyProblem
economicProblem =
  model-adequacy-problem
    FixtureWorld EconomicObservation EconomicOutcome
    economicObservation economicOutcome

ecologicalProblem : ModelAdequacyProblem
ecologicalProblem =
  model-adequacy-problem
    FixtureWorld EconomicObservation EcologicalOutcome
    economicObservation ecologicalOutcome

economicModelAdequate : ModelAdequateFor economicProblem
economicModelAdequate =
  INF.factorsThrough
    (λ _ → sameEconomicOutcome)
    λ { lowHydrology → refl ; highHydrology → refl }

ecologicalOutcomesDiffer :
  ecologicalOutcome lowHydrology ≡ ecologicalOutcome highHydrology → ⊥
ecologicalOutcomesDiffer ()

ecologicalInadequacyWitness : ModelInadequacyWitness ecologicalProblem
ecologicalInadequacyWitness =
  model-inadequacy-witness
    (INF.nonFactorabilityWitness
      lowHydrology
      highHydrology
      refl
      ecologicalOutcomesDiffer)

economicAdequacyDoesNotGiveEcologicalAdequacy :
  ModelAdequateFor ecologicalProblem → ⊥
economicAdequacyDoesNotGiveEcologicalAdequacy =
  inadequacyWitnessRulesOutAdequacy ecologicalInadequacyWitness

------------------------------------------------------------------------
-- Authority remains a distinct consumer/outcome family, not a model variable
-- inferred from technical richness.
------------------------------------------------------------------------

data MoreModelOutputImpliesMoreDecisionAuthorityPermission : Set where

data MoreAuthorityImpliesMoreEmpiricalAccuracyPermission : Set where

moreModelOutputDoesNotAutoPromoteToMoreDecisionAuthority :
  MoreModelOutputImpliesMoreDecisionAuthorityPermission → ⊥
moreModelOutputDoesNotAutoPromoteToMoreDecisionAuthority ()

moreAuthorityDoesNotAutoPromoteToMoreEmpiricalAccuracy :
  MoreAuthorityImpliesMoreEmpiricalAccuracyPermission → ⊥
moreAuthorityDoesNotAutoPromoteToMoreEmpiricalAccuracy ()

record ModelAdequacyBoundary : Set where
  constructor model-adequacy-boundary
  field
    adequacyIsConsumerRelative : Bool
    adequacyIsConsumerRelativeIsTrue : adequacyIsConsumerRelative ≡ true
    equalModelObservationCanHideDifferentConsumerOutcome : Bool
    equalModelObservationCanHideDifferentConsumerOutcomeIsTrue :
      equalModelObservationCanHideDifferentConsumerOutcome ≡ true
    moreOutputsCreateDecisionAuthority : Bool
    moreOutputsCreateDecisionAuthorityIsFalse : moreOutputsCreateDecisionAuthority ≡ false

canonicalModelAdequacyBoundary : ModelAdequacyBoundary
canonicalModelAdequacyBoundary =
  model-adequacy-boundary true refl true refl false refl
