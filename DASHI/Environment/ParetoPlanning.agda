module DASHI.Environment.ParetoPlanning where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)

import DASHI.Environment.InversePlanning as Planning

------------------------------------------------------------------------
-- Objective vectors and dominance.

data Direction : Set where
  minimise : Direction
  maximise : Direction

record ObjectiveScore : Set where
  constructor mkObjectiveScore
  field
    objectiveId : String
    direction : Direction
    value : Nat
    unitLabel : String
    evidenceReference : String
open ObjectiveScore public

scoreNoWorse : ObjectiveScore → ObjectiveScore → Set
scoreNoWorse a b with direction a | direction b
... | minimise | minimise = value a ≤ value b
... | maximise | maximise = value b ≤ value a
... | minimise | maximise = Bool
... | maximise | minimise = Bool

scoreStrictlyBetter : ObjectiveScore → ObjectiveScore → Set
scoreStrictlyBetter a b with direction a | direction b
... | minimise | minimise = value a < value b
... | maximise | maximise = value b < value a
... | minimise | maximise = Bool
... | maximise | minimise = Bool

data VectorNoWorse : List ObjectiveScore → List ObjectiveScore → Set where
  vector-empty : VectorNoWorse [] []
  vector-cons :
    ∀ {a b as bs} →
    objectiveId a ≡ objectiveId b →
    scoreNoWorse a b →
    VectorNoWorse as bs →
    VectorNoWorse (a ∷ as) (b ∷ bs)

data SomeStrictlyBetter : List ObjectiveScore → List ObjectiveScore → Set where
  strict-head :
    ∀ {a b as bs} →
    objectiveId a ≡ objectiveId b →
    scoreStrictlyBetter a b →
    SomeStrictlyBetter (a ∷ as) (b ∷ bs)
  strict-tail :
    ∀ {a b as bs} →
    objectiveId a ≡ objectiveId b →
    SomeStrictlyBetter as bs →
    SomeStrictlyBetter (a ∷ as) (b ∷ bs)

record EvaluatedPlan : Set where
  constructor mkEvaluatedPlan
  field
    plan : Planning.Plan
    hardConstraintsSatisfied : Bool
    objectiveVector : List ObjectiveScore
    evaluationProvenance : List String
open EvaluatedPlan public

record Dominates (better worse : EvaluatedPlan) : Set where
  constructor mkDominates
  field
    betterAdmissible : hardConstraintsSatisfied better ≡ true
    worseAdmissible : hardConstraintsSatisfied worse ≡ true
    noWorseOnAllObjectives :
      VectorNoWorse (objectiveVector better) (objectiveVector worse)
    strictlyBetterOnSomeObjective :
      SomeStrictlyBetter (objectiveVector better) (objectiveVector worse)
open Dominates public

record NonDominatedIn
       (candidate : EvaluatedPlan)
       (population : List EvaluatedPlan) : Set where
  constructor mkNonDominatedIn
  field
    candidateIsEnumerated : candidate ∈ population
    candidateIsAdmissible : hardConstraintsSatisfied candidate ≡ true
    noEnumeratorDominates :
      ∀ other →
      other ∈ population →
      Dominates other candidate →
      false ≡ true
open NonDominatedIn public

record FiniteParetoResult : Set where
  constructor mkFiniteParetoResult
  field
    candidatePopulation : List EvaluatedPlan
    nonDominatedCandidates : List EvaluatedPlan
    enumerationBound : Nat
    candidateGenerationRule : String
    tradeoffReport : List String
    noClaimOfUniqueOptimum : Bool
open FiniteParetoResult public

------------------------------------------------------------------------
-- Keep MDL and Pareto selection explicitly separate.

record SelectionSeparationBoundary : Set where
  constructor mkSelectionSeparationBoundary
  field
    mdlSelectsExplanationOrModelComplexity : Bool
    paretoSelectsAmongAdmissiblePlans : Bool
    weightsDoNotEraseReportedTradeoffs : Bool
    infeasiblePlansCannotDominate : Bool
    objectiveUnitsMustBeDeclared : Bool
open SelectionSeparationBoundary public

canonicalSelectionSeparationBoundary : SelectionSeparationBoundary
canonicalSelectionSeparationBoundary =
  mkSelectionSeparationBoundary true true true true true
