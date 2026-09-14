module DASHI.Core.RequirementConflictBatchExecutionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.RequirementConflictBatchExecutionExact as Batch

------------------------------------------------------------------------
-- RED/GREEN contract for the domain-neutral batch-execution spine extracted
-- from the RSA/NDim reducer lane.
------------------------------------------------------------------------

data Candidate : Set where c0 c1 : Candidate
data BatchCarrier : Set where batch01 : BatchCarrier
data GlobalAction : Set where composed01 : GlobalAction

spine : Batch.RequirementConflictBatchSpine
spine = record
  { Candidate = Candidate
  ; Batch = BatchCarrier
  ; GlobalAction = GlobalAction
  ; requirementClosed = λ batch → Bool
  ; conflictFree = λ batch → Bool
  ; compose = λ batch → composed01
  ; globallyValid = λ action → Bool
  }

admitted : Batch.AdmittedBatchExecution spine batch01
admitted = Batch.admitBatchExecution true true true

closureDoesNotEraseConflict : Bool
closureDoesNotEraseConflict =
  Batch.BatchExecutionBoundary.requirementClosureImpliesConflictFreedom
    Batch.canonicalBatchExecutionBoundary

closureDoesNotEraseConflictIsFalse : closureDoesNotEraseConflict ≡ false
closureDoesNotEraseConflictIsFalse = refl

globalValidityIsSeparate : Bool
globalValidityIsSeparate =
  Batch.BatchExecutionBoundary.closedConflictFreeBatchImpliesGlobalValidity
    Batch.canonicalBatchExecutionBoundary

globalValidityIsSeparateIsFalse : globalValidityIsSeparate ≡ false
globalValidityIsSeparateIsFalse = refl
