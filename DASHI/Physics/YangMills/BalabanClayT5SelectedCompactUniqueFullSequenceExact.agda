{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedCompactUniqueFullSequenceExact where

------------------------------------------------------------------------
-- SELECTED COMPACTNESS + UNIQUE CLUSTER POINT -> FULL CONVERGENCE
--
-- This is the least-privilege replacement for the historical compact-unique
-- compiler.  It uses only a convergence relation; no total limit operator and
-- no assertion that arbitrary sequences converge.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as Legacy
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected

record SelectedCompactUniqueData (Object : Set) : Set₁ where
  field
    convergence : Selected.SequentialConvergence Object
    sequence : Agda.Builtin.Nat.Nat → Object
    target : Object

    extractFurther :
      (subsequence : Legacy.SubsequenceWitness sequence) →
      Legacy.SubsequenceWitness (Legacy.values subsequence)

    clusterLimit : Legacy.SubsequenceWitness sequence → Object

    extractedSubsequenceConverges :
      (subsequence : Legacy.SubsequenceWitness sequence) →
      Selected.Converges convergence
        (Legacy.values (extractFurther subsequence))
        (clusterLimit subsequence)

    uniqueClusterPoint :
      (subsequence : Legacy.SubsequenceWitness sequence) →
      clusterLimit subsequence ≡ target

open SelectedCompactUniqueData public

record SelectedCompactUniqueFullConvergenceAuthority (Object : Set) : Set₁ where
  field
    compactUniqueImpliesFullConvergence :
      (dataSet : SelectedCompactUniqueData Object) →
      Selected.Converges
        (convergence dataSet)
        (sequence dataSet)
        (target dataSet)

open SelectedCompactUniqueFullConvergenceAuthority public

selectedFullSequenceConverges :
  ∀ {Object} →
  SelectedCompactUniqueFullConvergenceAuthority Object →
  (dataSet : SelectedCompactUniqueData Object) →
  Selected.Converges
    (convergence dataSet)
    (sequence dataSet)
    (target dataSet)
selectedFullSequenceConverges authority =
  compactUniqueImpliesFullConvergence authority

selectedCompactUniqueCompilerLevel : ProofLevel
selectedCompactUniqueCompilerLevel = machineChecked

selectedCompactUniqueAuthorityLevel : ProofLevel
selectedCompactUniqueAuthorityLevel = standardImported
