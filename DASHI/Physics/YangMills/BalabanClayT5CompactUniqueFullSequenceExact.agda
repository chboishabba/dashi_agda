{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact where

------------------------------------------------------------------------
-- COMPACTNESS + UNIQUE CLUSTER POINT -> FULL SEQUENCE CONVERGENCE
--
-- The older T5 compactness ledgers record subsequence existence and uniqueness
-- as Set-valued receipts.  Those do not by themselves inhabit the measure-level
-- convergence relation consumed by FiniteToContinuumOSClosure.
--
-- This module states the least-privilege typed theorem surface.  Once every
-- subsequence of the selected physical diagonal sequence has a further
-- convergent subsequence, and every such cluster point is the selected
-- continuum candidate, the standard compact/unique-limit theorem upgrades the
-- whole selected sequence to convergence.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit

record SequentialCompactUniqueData (Object : Set) : Set₁ where
  field
    convergence : Limit.SequentialLimit Object
    sequence : Nat → Object
    target : Object

    Subsequence : Set
    values : Subsequence → Nat → Object

    FurtherSubsequence : Subsequence → Set
    furtherValues : ∀ subsequence →
      FurtherSubsequence subsequence → Nat → Object

    -- Every subsequence has a further subsequence which converges in the same
    -- declared topology.  This is the typed relative sequential compactness
    -- statement needed by the standard theorem.
    relativelySequentiallyCompact : ∀ subsequence →
      FurtherSubsequence subsequence

    clusterLimit : ∀ subsequence →
      FurtherSubsequence subsequence → Object

    extractedSubsequenceConverges : ∀ subsequence →
      let further = relativelySequentiallyCompact subsequence
      in Limit.Converges convergence
        (furtherValues subsequence further)
        (clusterLimit subsequence further)

    -- Every cluster point of the selected sequence is the selected target.
    uniqueClusterPoint : ∀ subsequence →
      let further = relativelySequentiallyCompact subsequence
      in clusterLimit subsequence further ≡ target

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

-- This is a standard topology theorem authority, not Yang--Mills-specific
-- mathematics.  The physical work is instantiating the two typed premises on
-- the literal diagonal gauge-field measure sequence.
compactUniqueFullConvergenceAuthorityLevel : ProofLevel
compactUniqueFullConvergenceAuthorityLevel = standardImported

physicalRelativeSequentialCompactnessLevel : ProofLevel
physicalRelativeSequentialCompactnessLevel = conditional

physicalUniqueClusterPointLevel : ProofLevel
physicalUniqueClusterPointLevel = conditional
