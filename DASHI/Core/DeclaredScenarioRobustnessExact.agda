module DASHI.Core.DeclaredScenarioRobustnessExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Robustness is quantified over a declared scenario ensemble, not over every
-- inhabitant of an open-ended future type.  This module supplies the precise
-- ensemble-relative theorem and its monotonicity under scenario-set restriction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.List using (List)
open import Data.List.Membership.Propositional using (_∈_)

record RobustOnDeclared
    {Plan Future : Set}
    (Acceptable : Plan → Future → Set)
    (plan : Plan)
    (ensemble : List Future) : Set₁ where
  constructor robustOnDeclared
  field
    acceptableForMember :
      ∀ future →
      future ∈ ensemble →
      Acceptable plan future

open RobustOnDeclared public

robustnessRestrictsToSubensemble :
  ∀ {Plan Future}
    {Acceptable : Plan → Future → Set}
    {plan : Plan}
    {larger smaller : List Future} →
  RobustOnDeclared Acceptable plan larger →
  (∀ future → future ∈ smaller → future ∈ larger) →
  RobustOnDeclared Acceptable plan smaller
robustnessRestrictsToSubensemble robust included =
  robustOnDeclared λ future member →
    acceptableForMember robust future (included future member)

record DeclaredScenarioBoundary : Set where
  constructor declaredScenarioBoundary
  field
    robustnessQuantifiesOnlyDeclaredMembers : Bool
    addingScenariosCanCreateNewObligations : Bool
    removingScenariosCannotCreateARequirementForRemovedMembers : Bool
    scenarioMembershipDoesNotCreateProbabilityWeights : Bool

canonicalDeclaredScenarioBoundary : DeclaredScenarioBoundary
canonicalDeclaredScenarioBoundary =
  declaredScenarioBoundary true true true true
