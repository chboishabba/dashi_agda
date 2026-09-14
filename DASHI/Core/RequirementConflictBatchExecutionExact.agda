module DASHI.Core.RequirementConflictBatchExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Product using (_×_; _,_)

import DASHI.Core.CandidateFamilyExecutionExact as Family

------------------------------------------------------------------------
-- DOMAIN-NEUTRAL REQUIREMENT / CONFLICT / GLOBAL-EXECUTION SPINE
--
-- This is extracted from the recurring RSA/NDim batch-reduction shape without
-- importing RSA, GF(2), matrices, colouring, GPU, or performance semantics.
--
-- It specializes CandidateFamilyExecutionExact by defining family
-- admissibility as the conjunction of two logically separate payments:
--   * requirement closure,
--   * conflict freedom.
-- Global validity of the composed action remains a third independent payment.
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

asCandidateFamilyExecutionSpine :
  RequirementConflictBatchSpine →
  Family.CandidateFamilyExecutionSpine
asCandidateFamilyExecutionSpine spine = record
  { Family = Batch spine
  ; GlobalAction = GlobalAction spine
  ; admissibleFamily = λ batch →
      requirementClosed spine batch × conflictFree spine batch
  ; compose = compose spine
  ; globallyAdmissible = globallyValid spine
  }

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

admittedBatchProjectsToCandidateFamilyExecution :
  {spine : RequirementConflictBatchSpine} →
  {batch : Batch spine} →
  AdmittedBatchExecution spine batch →
  Family.AdmittedCandidateFamilyExecution
    (asCandidateFamilyExecutionSpine spine)
    batch
admittedBatchProjectsToCandidateFamilyExecution execution =
  Family.admitCandidateFamilyExecution
    (requirementClosurePaid execution , conflictFreedomPaid execution)
    (globalValidityPaid execution)

record BatchExecutionBoundary : Set where
  constructor batch-execution-boundary
  field
    candidateFamilyParentReused : Bool
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
    true
    false
    false
    false
    false
