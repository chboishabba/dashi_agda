{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact where

------------------------------------------------------------------------
-- COMPACTNESS + UNIQUE CLUSTER POINT -> FULL SEQUENCE CONVERGENCE
--
-- The older T5 compactness ledgers record subsequence existence and uniqueness
-- as Set-valued receipts.  Those do not by themselves inhabit the measure-level
-- convergence relation consumed by FiniteToContinuumOSClosure.
--
-- This module states the least-privilege typed theorem surface on literal
-- natural-number subsequences.  Every extracted object sequence is definitionally
-- obtained from the selected physical sequence by a Nat -> Nat index map.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit

record SubsequenceWitness {Object : Set}
    (sequence : Nat → Object) : Set₁ where
  field
    indices : Nat → Nat
    StrictlyIncreasing : (Nat → Nat) → Set
    indicesStrictlyIncreasing : StrictlyIncreasing indices

  values : Nat → Object
  values n = sequence (indices n)

open SubsequenceWitness public

record SequentialCompactUniqueData (Object : Set) : Set₁ where
  field
    convergence : Limit.SequentialLimit Object
    sequence : Nat → Object
    target : Object

    -- Relative sequential compactness: every literal subsequence admits a
    -- literal further subsequence.  Its values are therefore forced to be
    -- values of the original sequence, not an unrelated carrier.
    extractFurther :
      (subsequence : SubsequenceWitness sequence) →
      SubsequenceWitness (values subsequence)

    clusterLimit :
      (subsequence : SubsequenceWitness sequence) → Object

    extractedSubsequenceConverges :
      (subsequence : SubsequenceWitness sequence) →
      Limit.Converges convergence
        (values (extractFurther subsequence))
        (clusterLimit subsequence)

    -- Every cluster point extracted from every subsequence is the selected
    -- continuum target.
    uniqueClusterPoint :
      (subsequence : SubsequenceWitness sequence) →
      clusterLimit subsequence ≡ target

open SequentialCompactUniqueData public

record CompactUniqueFullConvergenceAuthority (Object : Set) : Set₁ where
  field
    compactUniqueImpliesFullConvergence :
      (dataSet : SequentialCompactUniqueData Object) →
      Limit.Converges
        (convergence dataSet)
        (sequence dataSet)
        (target dataSet)

open CompactUniqueFullConvergenceAuthority public

fullSequenceConverges :
  ∀ {Object} →
  CompactUniqueFullConvergenceAuthority Object →
  (dataSet : SequentialCompactUniqueData Object) →
  Limit.Converges
    (convergence dataSet)
    (sequence dataSet)
    (target dataSet)
fullSequenceConverges authority =
  compactUniqueImpliesFullConvergence authority

compactUniqueFullSequenceCompilerLevel : ProofLevel
compactUniqueFullSequenceCompilerLevel = machineChecked

-- Standard topology theorem authority.  The Yang--Mills work is the literal
-- instantiation of relative sequential compactness and uniqueness of cluster
-- points on the selected diagonal gauge-field measure sequence.
compactUniqueFullConvergenceAuthorityLevel : ProofLevel
compactUniqueFullConvergenceAuthorityLevel = standardImported

physicalRelativeSequentialCompactnessLevel : ProofLevel
physicalRelativeSequentialCompactnessLevel = conditional

physicalUniqueClusterPointLevel : ProofLevel
physicalUniqueClusterPointLevel = conditional
