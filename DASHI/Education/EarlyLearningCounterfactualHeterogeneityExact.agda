module DASHI.Education.EarlyLearningCounterfactualHeterogeneityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Education.EarlyLearningComparativeArchitectureExact as Architecture

------------------------------------------------------------------------
-- COUNTERFACTUAL-RELATIVE POLICY EFFECTS
--
-- Comparative ECEC evidence does not support a context-free function
--
--   intervention label -> developmental effect.
--
-- The same nominal intervention can replace very different counterfactual care
-- environments.  This module captures only that structural identification
-- boundary; the finite values below are witnesses, not population estimates.
------------------------------------------------------------------------

data InterventionLabel : Set where
  expandedSubsidisedECEC : InterventionLabel

data ObservedFamilyPosition : Set where
  observedHigherResource observedLowerResource : ObservedFamilyPosition

data HiddenCounterfactual : Set where
  strongerAlternativeCare weakerAlternativeCare : HiddenCounterfactual

data EffectDirection : Set where
  adverseDirection beneficialDirection : EffectDirection

record SituatedExposure : Set where
  constructor situatedExposure
  field
    intervention : InterventionLabel
    observedPosition : ObservedFamilyPosition
    counterfactual : HiddenCounterfactual

open SituatedExposure public

higherCounterfactualExposure : SituatedExposure
higherCounterfactualExposure =
  situatedExposure expandedSubsidisedECEC observedHigherResource strongerAlternativeCare

lowerCounterfactualExposure : SituatedExposure
lowerCounterfactualExposure =
  situatedExposure expandedSubsidisedECEC observedLowerResource weakerAlternativeCare

interventionProjection : SituatedExposure → InterventionLabel
interventionProjection = intervention

counterfactualRelativeEffect : SituatedExposure → EffectDirection
counterfactualRelativeEffect higherCounterfactualExposure = adverseDirection
counterfactualRelativeEffect lowerCounterfactualExposure = beneficialDirection
counterfactualRelativeEffect _ = adverseDirection

sameInterventionDifferentEffect :
  counterfactualRelativeEffect higherCounterfactualExposure ≡
  counterfactualRelativeEffect lowerCounterfactualExposure → ⊥
sameInterventionDifferentEffect ()

interventionEffectNonFactorability :
  Intersection.NonFactorabilityWitness
    interventionProjection counterfactualRelativeEffect
interventionEffectNonFactorability =
  Intersection.nonFactorabilityWitness
    higherCounterfactualExposure
    lowerCounterfactualExposure
    refl
    sameInterventionDifferentEffect

interventionLabelCannotDetermineEffect :
  Intersection.FactorsThrough
    interventionProjection counterfactualRelativeEffect → ⊥
interventionLabelCannotDetermineEffect =
  Intersection.witnessRulesOutEveryFlatFactorisation
    interventionEffectNonFactorability

------------------------------------------------------------------------
-- A demographic/subgroup label is also not promoted into a deterministic
-- routing rule.  Two states can share the same observed group while differing
-- in an unobserved/home-learning counterfactual that matters to effect.
------------------------------------------------------------------------

data CommonObservedGroup : Set where
  sameObservedGroup : CommonObservedGroup

data WithinGroupState : Set where
  groupBetterCounterfactual groupWorseCounterfactual : WithinGroupState

observedGroupProjection : WithinGroupState → CommonObservedGroup
observedGroupProjection groupBetterCounterfactual = sameObservedGroup
observedGroupProjection groupWorseCounterfactual = sameObservedGroup

withinGroupEffect : WithinGroupState → EffectDirection
withinGroupEffect groupBetterCounterfactual = adverseDirection
withinGroupEffect groupWorseCounterfactual = beneficialDirection

withinGroupEffectsDiffer :
  withinGroupEffect groupBetterCounterfactual ≡
  withinGroupEffect groupWorseCounterfactual → ⊥
withinGroupEffectsDiffer ()

observedGroupCannotDetermineIndividualEffect :
  Intersection.FactorsThrough observedGroupProjection withinGroupEffect → ⊥
observedGroupCannotDetermineIndividualEffect =
  Intersection.witnessRulesOutEveryFlatFactorisation
    (Intersection.nonFactorabilityWitness
      groupBetterCounterfactual
      groupWorseCounterfactual
      refl
      withinGroupEffectsDiffer)

------------------------------------------------------------------------
-- Reuse the existing architecture result: even retaining the professional
-- floor does not collapse quality, rollout and family counterfactuals.
------------------------------------------------------------------------

professionalFloorStillCannotDetermineOutcome :
  Intersection.FactorsThrough
    Architecture.professionalFloorProjection
    Architecture.comparativeOutcomeWitness → ⊥
professionalFloorStillCannotDetermineOutcome =
  Architecture.professionalFloorCannotDetermineOutcome

record CounterfactualHeterogeneityBoundary : Set where
  constructor counterfactualHeterogeneityBoundary
  field
    sameInterventionCanHaveDifferentSituatedEffects : Bool
    sameInterventionCanHaveDifferentSituatedEffectsIsTrue :
      sameInterventionCanHaveDifferentSituatedEffects ≡ true
    subgroupLabelDeterminesIndividualEffect : Bool
    subgroupLabelDeterminesIndividualEffectIsFalse :
      subgroupLabelDeterminesIndividualEffect ≡ false
    counterfactualCareIsOutcomeRelevantCoordinate : Bool
    counterfactualCareIsOutcomeRelevantCoordinateIsTrue :
      counterfactualCareIsOutcomeRelevantCoordinate ≡ true

canonicalCounterfactualHeterogeneityBoundary : CounterfactualHeterogeneityBoundary
canonicalCounterfactualHeterogeneityBoundary =
  counterfactualHeterogeneityBoundary true refl false refl true refl
