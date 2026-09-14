module DASHI.Core.RequirementConflictBatchExecutionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.CandidateFamilyExecutionExact as Family
import DASHI.Core.RequirementConflictBatchExecutionExact as Batch

------------------------------------------------------------------------
-- RED/GREEN contract for the domain-neutral batch-execution spine extracted
-- from the RSA/NDim reducer lane.
------------------------------------------------------------------------

data Candidate : Set where c0 c1 : Candidate
data BatchCarrier : Set where batch01 : BatchCarrier
data GlobalAction : Set where composed01 : GlobalAction

conflictRelation : Batch.CandidateRelation
conflictRelation = Batch.conflict

coRequirementRelation : Batch.CandidateRelation
coRequirementRelation = Batch.coRequirement

independentRelation : Batch.CandidateRelation
independentRelation = Batch.independent

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

projectedToGenericFamilyExecution :
  Family.AdmittedCandidateFamilyExecution
    (Batch.asCandidateFamilyExecutionSpine spine)
    batch01
projectedToGenericFamilyExecution =
  Batch.admittedBatchProjectsToCandidateFamilyExecution admitted

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

relationKnowledgeMayBePartial : Bool
relationKnowledgeMayBePartial =
  Batch.BatchExecutionBoundary.relationKnowledgeRequiredToBeTotal
    Batch.canonicalBatchExecutionBoundary

relationKnowledgeMayBePartialIsFalse : relationKnowledgeMayBePartial ≡ false
relationKnowledgeMayBePartialIsFalse = refl
