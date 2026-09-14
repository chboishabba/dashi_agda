module DASHI.ComputerScience.RSA260RequirementConflictBatchSpineRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.RequirementConflictBatchExecutionExact as Batch
import DASHI.ComputerScience.RSA260RequirementConflictBatchSpineExact as Adapter

rsaBatchSpine : Batch.RequirementConflictBatchSpine
rsaBatchSpine = Adapter.rsaSyntheticBatchSpine

rsaSyntheticBatchAdmitted :
  Batch.AdmittedBatchExecution
    rsaBatchSpine
    Adapter.syntheticBatchReceipt
rsaSyntheticBatchAdmitted = Adapter.syntheticBatchExecution

productionClaimed : Bool
productionClaimed =
  Adapter.RSARequirementConflictBatchBoundary.productionRSA260ExecutionClaimed
    Adapter.canonicalRSARequirementConflictBatchBoundary

productionClaimedIsFalse : productionClaimed ≡ false
productionClaimedIsFalse = refl
