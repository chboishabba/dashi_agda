module DASHI.Core.RequirementConflictBatchExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- DOMAIN-NEUTRAL REQUIREMENT / CONFLICT / GLOBAL-EXECUTION SPINE
--
-- This is extracted from the recurring RSA/NDim batch-reduction shape without
-- importing RSA, GF(2), matrices, colouring, GPU, or performance semantics.
--
-- A batch is admitted only after three logically separate payments:
--   * requirement closure,
--   * conflict freedom,
--   * global validity of the composed action.
--
-- The record deliberately does NOT provide maps from one payment to another.
------------------------------------------------------------------------

record RequirementConflictBatchSpine : Set₁ where
  field
    Candidate : Set
    Batch : Set
    GlobalAction : Set

    requirementClosed : Batch → Set
    conflictFree : Batch → Set

    compose : Batch → GlobalAction
    globallyValid : GlobalAction → Set

open RequirementConflictBatchSpine public

record AdmittedBatchExecution
    (spine : RequirementConflictBatchSpine)
    (batch : Batch spine) : Set where
  constructor admitted-batch-execution
  field
    requirementClosurePaid : requirementClosed spine batch
    conflictFreedomPaid : conflictFree spine batch
    globalValidityPaid : globallyValid spine (compose spine batch)

open AdmittedBatchExecution public

admitBatchExecution :
  {spine : RequirementConflictBatchSpine} →
  {batch : Batch spine} →
  requirementClosed spine batch →
  conflictFree spine batch →
  globallyValid spine (compose spine batch) →
  AdmittedBatchExecution spine batch
admitBatchExecution = admitted-batch-execution

record BatchExecutionBoundary : Set where
  constructor batch-execution-boundary
  field
    requirementClosureRequired : Bool
    conflictFreedomRequired : Bool
    globalValidityRequiredAfterSelection : Bool
    requirementClosureImpliesConflictFreedom : Bool
    conflictFreedomImpliesRequirementClosure : Bool
    closedConflictFreeBatchImpliesGlobalValidity : Bool
    domainSpecificAlgebraBuiltIntoSpine : Bool

canonicalBatchExecutionBoundary : BatchExecutionBoundary
canonicalBatchExecutionBoundary =
  batch-execution-boundary
    true
    true
    true
    false
    false
    false
    false
