module DASHI.Core.PluralPreferenceNonCollapseExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- A Pareto front is a technical feasibility/trade-off object, not a unique
-- stakeholder preference.  This module gives an exact two-stakeholder
-- countermodel: both plans can remain technically admissible while stakeholder
-- strict preferences point in opposite directions.  No selector can be
-- presented as unanimous without additional aggregation/governance rules.
--
-- REFERENCE / MOTIVATION
--
-- Ivy B. Huang, Jennifer Keisler, Igor Linkov,
-- "Multi-criteria decision analysis in environmental sciences: Ten years of
-- applications and trends",
-- Science of the Total Environment 409 (2011), 3578-3594.
-- DOI: 10.1016/j.scitotenv.2011.06.022.
--
-- The source motivates explicit stakeholder-value treatment.  The finite
-- impossibility witness below is a DASHI construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Data.Empty using (⊥)


data Stakeholder : Set where
  waterCustodian habitatCustodian : Stakeholder

data Plan : Set where
  waterPlan habitatPlan : Plan

data StrictPreference : Stakeholder → Plan → Plan → Set where
  waterPrefersWater : StrictPreference waterCustodian waterPlan habitatPlan
  habitatPrefersHabitat : StrictPreference habitatCustodian habitatPlan waterPlan

record UnanimousStrictWinner (winner loser : Plan) : Set where
  constructor unanimousStrictWinner
  field
    waterStrictlyPrefers : StrictPreference waterCustodian winner loser
    habitatStrictlyPrefers : StrictPreference habitatCustodian winner loser

waterPlanCannotBeUnanimousStrictWinner :
  UnanimousStrictWinner waterPlan habitatPlan → ⊥
waterPlanCannotBeUnanimousStrictWinner
  (unanimousStrictWinner waterPrefersWater ())

habitatPlanCannotBeUnanimousStrictWinner :
  UnanimousStrictWinner habitatPlan waterPlan → ⊥
habitatPlanCannotBeUnanimousStrictWinner
  (unanimousStrictWinner () habitatPrefersHabitat)

noUnanimousStrictWinner :
  (winner : Plan) →
  (loser : Plan) →
  UnanimousStrictWinner winner loser →
  ⊥
noUnanimousStrictWinner waterPlan waterPlan
  (unanimousStrictWinner () habitatPreference)
noUnanimousStrictWinner waterPlan habitatPlan unanimous =
  waterPlanCannotBeUnanimousStrictWinner unanimous
noUnanimousStrictWinner habitatPlan waterPlan unanimous =
  habitatPlanCannotBeUnanimousStrictWinner unanimous
noUnanimousStrictWinner habitatPlan habitatPlan
  (unanimousStrictWinner waterPreference ())

record PreferenceNonCollapseBoundary : Set where
  constructor preferenceNonCollapseBoundary
  field
    technicalNonDominanceDoesNotDeterminePreference : Bool
    differentStakeholdersCanStrictlyPreferOppositePlans : Bool
    unanimousChoiceNeedsMoreThanAFront : Bool
    aggregationRuleRequiresIndependentJustification : Bool

canonicalPreferenceNonCollapseBoundary : PreferenceNonCollapseBoundary
canonicalPreferenceNonCollapseBoundary =
  preferenceNonCollapseBoundary true true true true
