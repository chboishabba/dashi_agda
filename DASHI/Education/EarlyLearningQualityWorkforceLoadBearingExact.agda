module DASHI.Education.EarlyLearningQualityWorkforceLoadBearingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Education.EarlyLearningComparativeArchitectureExact as Architecture

------------------------------------------------------------------------
-- QUALITY / WORKFORCE LOAD-BEARING BOUNDARY
--
-- The comparative carrier already distinguishes professional relation,
-- quality, rollout and counterfactual home state.  Here we make two missing
-- non-factorability consequences explicit: professional presence does not
-- determine actual quality, and entitlement does not determine rollout
-- capacity.
------------------------------------------------------------------------

professionalRelationProjection :
  Architecture.ComparativeLearningArchitecture → Architecture.ProfessionalRelation
professionalRelationProjection = Architecture.professionalRelation

qualityProjection :
  Architecture.ComparativeLearningArchitecture → Architecture.QualityState
qualityProjection = Architecture.quality

sameProfessionalRelationDifferentQuality :
  qualityProjection Architecture.quebecRapidUniversalWitness ≡
  qualityProjection Architecture.matureHighQualityUniversalWitness → ⊥
sameProfessionalRelationDifferentQuality ()

professionalRelationQualityNonFactorability :
  Intersection.NonFactorabilityWitness
    professionalRelationProjection qualityProjection
professionalRelationQualityNonFactorability =
  Intersection.nonFactorabilityWitness
    Architecture.quebecRapidUniversalWitness
    Architecture.matureHighQualityUniversalWitness
    refl
    sameProfessionalRelationDifferentQuality

professionalPresenceCannotDetermineQuality :
  Intersection.FactorsThrough
    professionalRelationProjection qualityProjection → ⊥
professionalPresenceCannotDetermineQuality =
  Intersection.witnessRulesOutEveryFlatFactorisation
    professionalRelationQualityNonFactorability

entitlementProjection :
  Architecture.ComparativeLearningArchitecture → Bool
entitlementProjection = Architecture.childEntitlementRetained

rolloutProjection :
  Architecture.ComparativeLearningArchitecture → Architecture.RolloutState
rolloutProjection = Architecture.rollout

sameEntitlementDifferentRollout :
  rolloutProjection Architecture.quebecRapidUniversalWitness ≡
  rolloutProjection Architecture.matureHighQualityUniversalWitness → ⊥
sameEntitlementDifferentRollout ()

entitlementRolloutNonFactorability :
  Intersection.NonFactorabilityWitness entitlementProjection rolloutProjection
entitlementRolloutNonFactorability =
  Intersection.nonFactorabilityWitness
    Architecture.quebecRapidUniversalWitness
    Architecture.matureHighQualityUniversalWitness
    refl
    sameEntitlementDifferentRollout

universalEntitlementCannotDetermineRolloutCapacity :
  Intersection.FactorsThrough entitlementProjection rolloutProjection → ⊥
universalEntitlementCannotDetermineRolloutCapacity =
  Intersection.witnessRulesOutEveryFlatFactorisation
    entitlementRolloutNonFactorability

------------------------------------------------------------------------
-- Process quality is not identified with either setting or credential label.
------------------------------------------------------------------------

data ProcessQualityState : Set where
  processQualityUnknown constrainedInteractions richAdaptiveInteractions : ProcessQualityState

data WorkforceCapacityState : Set where
  workforceConstrained workforceSustainable : WorkforceCapacityState

record QualityCapacityGate : Set where
  constructor qualityCapacityGate
  field
    professionalRelationAvailable : Bool
    workforceCapacity : WorkforceCapacityState
    processQuality : ProcessQualityState
    adaptiveContextReview : Bool
    rolloutMature : Bool
    publicEntitlementRetained : Bool

open QualityCapacityGate public

matureQualityOpportunity : QualityCapacityGate
matureQualityOpportunity =
  qualityCapacityGate
    true workforceSustainable richAdaptiveInteractions true true true

rapidCapacityStress : QualityCapacityGate
rapidCapacityStress =
  qualityCapacityGate
    true workforceConstrained constrainedInteractions false false true

professionalGateProjection : QualityCapacityGate → Bool
professionalGateProjection = professionalRelationAvailable

processQualityAtGate : QualityCapacityGate → ProcessQualityState
processQualityAtGate = processQuality

processQualityDiffersAtSameProfessionalGate :
  processQualityAtGate matureQualityOpportunity ≡
  processQualityAtGate rapidCapacityStress → ⊥
processQualityDiffersAtSameProfessionalGate ()

professionalGateCannotDetermineProcessQuality :
  Intersection.FactorsThrough professionalGateProjection processQualityAtGate → ⊥
professionalGateCannotDetermineProcessQuality =
  Intersection.witnessRulesOutEveryFlatFactorisation
    (Intersection.nonFactorabilityWitness
      matureQualityOpportunity rapidCapacityStress refl
      processQualityDiffersAtSameProfessionalGate)

------------------------------------------------------------------------
-- Positive gate discipline: the richer quality carrier identifies conditions
-- worth preserving/monitoring, but it does not itself manufacture an outcome
-- theorem.
------------------------------------------------------------------------

data QualityGateOutcomeAuthority : Set where

qualityGateCannotAutoPromoteToBeneficialOutcome :
  QualityGateOutcomeAuthority → ⊥
qualityGateCannotAutoPromoteToBeneficialOutcome ()

record QualityWorkforceBoundary : Set where
  constructor qualityWorkforceBoundary
  field
    professionalPresenceEqualsQuality : Bool
    professionalPresenceEqualsQualityIsFalse :
      professionalPresenceEqualsQuality ≡ false
    entitlementEqualsMatureCapacity : Bool
    entitlementEqualsMatureCapacityIsFalse :
      entitlementEqualsMatureCapacity ≡ false
    workforceAndProcessQualityRemainExplicit : Bool
    workforceAndProcessQualityRemainExplicitIsTrue :
      workforceAndProcessQualityRemainExplicit ≡ true

canonicalQualityWorkforceBoundary : QualityWorkforceBoundary
canonicalQualityWorkforceBoundary =
  qualityWorkforceBoundary false refl false refl true refl
