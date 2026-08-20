module DASHI.Environment.BoundedParetoCompletenessExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- `NonDominatedIn` only speaks about the generated population.  This module
-- proves the missing bounded-search theorem: if an enumeration is complete for
-- the declared admissible intervention language, non-dominance in that list
-- implies absence of any admissible dominator in that declared language.
--
-- It also keeps Pareto completeness separate from preference selection.
--
-- REFERENCE / MOTIVATION
--
-- Ivy B. Huang, Jennifer Keisler, Igor Linkov,
-- "Multi-criteria decision analysis in environmental sciences: Ten years of
-- applications and trends",
-- Science of the Total Environment 409 (2011), 3578-3594.
-- DOI: 10.1016/j.scitotenv.2011.06.022.
--
-- The source motivates explicit preference/MCDA separation.  The bounded
-- completeness theorem below is the DASHI construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core
import DASHI.Environment.ParetoPlanning as Pareto

record BoundedParetoComplete
    (Admissible : Pareto.EvaluatedPlan → Set)
    (candidate : Pareto.EvaluatedPlan) : Set₁ where
  constructor boundedParetoComplete
  field
    noAdmissiblePlanDominates :
      ∀ other →
      Admissible other →
      Pareto.Dominates other candidate →
      ⊥

open BoundedParetoComplete public

completeEnumerationLiftsNonDominance :
  ∀ {Admissible : Pareto.EvaluatedPlan → Set}
    {candidate : Pareto.EvaluatedPlan}
    (enumeration : Core.BoundedEnumeration Admissible) →
  Pareto.NonDominatedIn candidate (Core.enumerated enumeration) →
  BoundedParetoComplete Admissible candidate
completeEnumerationLiftsNonDominance enumeration nonDominated =
  boundedParetoComplete noDominator
  where
    noDominator :
      ∀ other →
      Admissible other →
      Pareto.Dominates other candidate →
      ⊥
    noDominator other admissible dominates =
      Pareto.noEnumeratorDominates nonDominated other
        (Core.completeRelativeToDeclaredLanguage enumeration other admissible)
        dominates

------------------------------------------------------------------------
-- Pareto front != preference choice: one fixed two-plan front admits opposite
-- selectors.  This is not a normative theorem; it is an exact non-uniqueness
-- witness showing why a preference/authority layer is additional information.
------------------------------------------------------------------------

data DemoTradeoffPlan : Set where
  waterFirst habitatFirst : DemoTradeoffPlan

record PreferenceSelector : Set where
  constructor preferenceSelector
  field
    choose : DemoTradeoffPlan
    preferenceBasis : DemoTradeoffPlan → Bool

open PreferenceSelector public

waterPreference : PreferenceSelector
waterPreference = preferenceSelector waterFirst λ where
  waterFirst → true
  habitatFirst → true

habitatPreference : PreferenceSelector
habitatPreference = preferenceSelector habitatFirst λ where
  waterFirst → true
  habitatFirst → true

sameFrontAllowsDifferentSelections :
  choose waterPreference ≡ choose habitatPreference → ⊥
sameFrontAllowsDifferentSelections ()

record BoundedParetoBoundary : Set where
  constructor boundedParetoBoundary
  field
    populationNonDominanceNeedsEnumerationCompletenessForGlobalClaim : Bool
    boundedCompletenessIsRelativeToDeclaredLanguage : Bool
    boundedCompletenessDoesNotImplyContinuousGlobalOptimality : Bool
    paretoCompletenessDoesNotSupplyPreferenceSelection : Bool

canonicalBoundedParetoBoundary : BoundedParetoBoundary
canonicalBoundedParetoBoundary =
  boundedParetoBoundary true true true true
