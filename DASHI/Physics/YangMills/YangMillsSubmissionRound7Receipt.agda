module DASHI.Physics.YangMills.YangMillsSubmissionRound7Receipt where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ)

import DASHI.Physics.YangMills.YangMillsSubmissionObligationCardinalityExact as Counts
import DASHI.Physics.YangMills.BalabanP06OwnedGraphCombinatoricsExact as P06
import DASHI.Physics.YangMills.BalabanP11UniformAbsorptionReductionExact as P11
import DASHI.Physics.YangMills.BalabanLargeFieldSuppression as LargeField
open import DASHI.Physics.YangMills.CompactLieProofLevel

record SubmissionRound7Receipt : Set₁ where
  field
    theoremSpineCount : ℕ
    theoremSpineCountExact : theoremSpineCount ≡ 191

    fullSubmissionCount : ℕ
    fullSubmissionCountExact : fullSubmissionCount ≡ 219

    ownedP06GraphKernel : P06.OwnedP06GraphCombinatorics

    p11AbsorptionReducer :
      P11.P11UniformAbsorptionInputs →
      LargeField.ImportedAbsorptionCondition

    countAuditLevel : ProofLevel
    p06GraphKernelLevel : ProofLevel
    p11ReducerLevel : ProofLevel
    endpointDefinitionsLevel : ProofLevel
    remainingInhabitantsLevel : ProofLevel

open SubmissionRound7Receipt public

currentSubmissionRound7Receipt : SubmissionRound7Receipt
currentSubmissionRound7Receipt = record
  { theoremSpineCount = Counts.theoremSpineObligationCount
  ; theoremSpineCountExact = Counts.theoremSpineObligationCountExact
  ; fullSubmissionCount = Counts.fullSubmissionObligationCount
  ; fullSubmissionCountExact = Counts.fullSubmissionObligationCountExact
  ; ownedP06GraphKernel = P06.currentOwnedP06GraphCombinatorics
  ; p11AbsorptionReducer = P11.p11AbsorptionConditionFromUniformMinimum
  ; countAuditLevel = machineChecked
  ; p06GraphKernelLevel = machineChecked
  ; p11ReducerLevel = machineChecked
  ; endpointDefinitionsLevel = machineChecked
  ; remainingInhabitantsLevel = conditional
  }
