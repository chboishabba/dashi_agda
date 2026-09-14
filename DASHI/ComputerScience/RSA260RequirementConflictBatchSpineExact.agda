module DASHI.ComputerScience.RSA260RequirementConflictBatchSpineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.RequirementConflictBatchExecutionExact as Batch
import DASHI.ComputerScience.RSA260FractalPadicHyperfabricBatchGluingExact as RSA

------------------------------------------------------------------------
-- RSA SYNTHETIC BATCH -> DOMAIN-NEUTRAL REQUIREMENT/CONFLICT SPINE
--
-- The current synthetic receipt is used only as a concrete inhabitant of the
-- generic execution shape.  It does not promote the benchmark to production
-- RSA-260 or import GF(2)/CUDA semantics into the core spine.
------------------------------------------------------------------------

syntheticBatchReceipt : RSA.BatchGluingClosureReceipt
syntheticBatchReceipt = RSA.currentBatchGluingClosureReceipt

rsaSyntheticBatchSpine : Batch.RequirementConflictBatchSpine
rsaSyntheticBatchSpine = record
  { Candidate = RSA.HierarchicalReducerCandidate
  ; Batch = RSA.BatchGluingClosureReceipt
  ; GlobalAction = RSA.BatchGluingClosureReceipt
  ; requirementClosed = λ receipt →
      RSA.allSeedClosuresReachGlobalFamily receipt
      ≡ RSA.closureFromOneSeed receipt
  ; conflictFree = λ receipt →
      RSA.conflictEdges receipt ≡ 0
  ; compose = λ receipt → receipt
  ; globallyValid = λ receipt →
      RSA.globalClosedFamilyCommutes receipt ≡ true
  }

syntheticRequirementClosurePaid :
  Batch.requirementClosed rsaSyntheticBatchSpine syntheticBatchReceipt
syntheticRequirementClosurePaid = refl

syntheticConflictFreedomPaid :
  Batch.conflictFree rsaSyntheticBatchSpine syntheticBatchReceipt
syntheticConflictFreedomPaid = refl

syntheticGlobalValidityPaid :
  Batch.globallyValid
    rsaSyntheticBatchSpine
    (Batch.compose rsaSyntheticBatchSpine syntheticBatchReceipt)
syntheticGlobalValidityPaid = refl

syntheticBatchExecution :
  Batch.AdmittedBatchExecution
    rsaSyntheticBatchSpine
    syntheticBatchReceipt
syntheticBatchExecution =
  Batch.admitBatchExecution
    syntheticRequirementClosurePaid
    syntheticConflictFreedomPaid
    syntheticGlobalValidityPaid

record RSARequirementConflictBatchBoundary : Set where
  constructor rsa-requirement-conflict-batch-boundary
  field
    genericSpineReused : Bool
    requirementClosurePaidSeparately : Bool
    conflictFreedomPaidSeparately : Bool
    globalCommutationPaidSeparately : Bool
    exactGitBlobExecutionPaid : Bool
    productionRSA260ExecutionClaimed : Bool
    gf2SemanticsPromotedIntoGenericSpine : Bool

canonicalRSARequirementConflictBatchBoundary :
  RSARequirementConflictBatchBoundary
canonicalRSARequirementConflictBatchBoundary =
  rsa-requirement-conflict-batch-boundary
    true
    true
    true
    true
    false
    false
    false
