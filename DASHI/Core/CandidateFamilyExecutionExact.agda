module DASHI.Core.CandidateFamilyExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

------------------------------------------------------------------------
-- DOMAIN-NEUTRAL CANDIDATE-FAMILY EXECUTION
--
-- A selected family may be locally admissible/compatible without its composed
-- action being globally admissible.  This parent spine records exactly that
-- separation.  Domain-specific notions such as conflicts, co-requirements,
-- held-out validity, operator equivariance, graph colouring, or GF(2) remain
-- downstream refinements of the two proof obligations.
------------------------------------------------------------------------

record CandidateFamilyExecutionSpine : Set₁ where
  field
    Family : Set
    GlobalAction : Set
    admissibleFamily : Family → Set
    compose : Family → GlobalAction
    globallyAdmissible : GlobalAction → Set

open CandidateFamilyExecutionSpine public

record AdmittedCandidateFamilyExecution
    (spine : CandidateFamilyExecutionSpine)
    (family : Family spine) : Set where
  constructor admitted-candidate-family-execution
  field
    familyAdmissibilityPaid : admissibleFamily spine family
    globalAdmissibilityPaid :
      globallyAdmissible spine (compose spine family)

open AdmittedCandidateFamilyExecution public

admitCandidateFamilyExecution :
  {spine : CandidateFamilyExecutionSpine} →
  {family : Family spine} →
  admissibleFamily spine family →
  globallyAdmissible spine (compose spine family) →
  AdmittedCandidateFamilyExecution spine family
admitCandidateFamilyExecution = admitted-candidate-family-execution

record CandidateFamilyExecutionBoundary : Set where
  constructor candidate-family-execution-boundary
  field
    familyAdmissibilityRequired : Bool
    globalAdmissibilityRequiredSeparately : Bool
    familyAdmissibilityImpliesGlobalAdmissibility : Bool
    globalExecutionImpliesEmpiricalSuccess : Bool
    domainSpecificRelationBuiltIntoParent : Bool

canonicalCandidateFamilyExecutionBoundary :
  CandidateFamilyExecutionBoundary
canonicalCandidateFamilyExecutionBoundary =
  candidate-family-execution-boundary
    true
    true
    false
    false
    false
