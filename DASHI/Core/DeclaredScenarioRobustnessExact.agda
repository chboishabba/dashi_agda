module DASHI.Core.DeclaredScenarioRobustnessExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Robustness is quantified over a declared scenario ensemble, not over every
-- inhabitant of an open-ended future type.  This module supplies the precise
-- ensemble-relative theorem and its monotonicity under scenario-set restriction.
--
-- A historical/universal interface can always be weakened into this declared
-- interface.  The converse is intentionally unavailable without an additional
-- coverage argument establishing that the declared ensemble exhausts the
-- relevant universe.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
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

------------------------------------------------------------------------
-- Least-privilege quantifier bridge.
--
-- This is the generic shape exposed again by the scoped second-moment work:
-- a stronger ambient/universal obligation can be consumed wherever only the
-- declared finite family is required.  No reverse map is provided.
------------------------------------------------------------------------

fromUniversalObligation :
  ∀ {Plan Future}
    {Acceptable : Plan → Future → Set}
    {plan : Plan}
    {ensemble : List Future} →
  ((future : Future) → Acceptable plan future) →
  RobustOnDeclared Acceptable plan ensemble
fromUniversalObligation universal =
  robustOnDeclared (λ future member → universal future)

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

universalObligationCanPayDeclaredFamily : Bool
universalObligationCanPayDeclaredFamily = true

declaredFamilyAutomaticallyRecoversUniversalObligation : Bool
declaredFamilyAutomaticallyRecoversUniversalObligation = false
