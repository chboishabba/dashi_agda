{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.DualModeSemanticExecutionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- BULK BOOTSTRAP AND INCREMENTAL EXECUTION SHARE SEMANTICS, NOT PLANS
--
-- The same semantic workload may have two deliberately different physical
-- realizations:
--
--   bulk bootstrap      : tranche-wide batching / sorting / set-wise execution
--   incremental runtime : sparse reopening / dependency-directed local work
--
-- Their common obligation is exact authority, not instruction-by-instruction
-- parity.  Requiring one physical plan for both workloads is therefore not part
-- of the semantic contract.
------------------------------------------------------------------------

record DualModeSemanticExecution
  (Workload Authority BulkReceipt IncrementalReceipt Store : Set) : Set₁ where
  field
    semanticAuthority : Workload → Authority

    bulkCompile : Workload → Authority
    incrementalCompile : Workload → Authority

    bulkExact :
      (workload : Workload) →
      bulkCompile workload ≡ semanticAuthority workload

    incrementalExact :
      (workload : Workload) →
      incrementalCompile workload ≡ semanticAuthority workload

    bulkReceipt : Workload → BulkReceipt
    incrementalReceipt : Workload → IncrementalReceipt

    -- PostgreSQL/persistent authority may be shared even though physical
    -- compilation plans differ before publication.
    publish : Authority → Store

open DualModeSemanticExecution public

bulkAndIncrementalAuthoritiesAgree :
  ∀ {Workload Authority BulkReceipt IncrementalReceipt Store : Set}
    (system : DualModeSemanticExecution
      Workload Authority BulkReceipt IncrementalReceipt Store)
    (workload : Workload) →
  bulkCompile system workload ≡ incrementalCompile system workload
bulkAndIncrementalAuthoritiesAgree system workload
  rewrite bulkExact system workload
        | incrementalExact system workload = refl

bulkAndIncrementalPublicationAgree :
  ∀ {Workload Authority BulkReceipt IncrementalReceipt Store : Set}
    (system : DualModeSemanticExecution
      Workload Authority BulkReceipt IncrementalReceipt Store)
    (workload : Workload) →
  publish system (bulkCompile system workload)
    ≡ publish system (incrementalCompile system workload)
bulkAndIncrementalPublicationAgree system workload
  rewrite bulkAndIncrementalAuthoritiesAgree system workload = refl

consumerObservationAgreesAcrossModes :
  ∀ {Workload Authority BulkReceipt IncrementalReceipt Store Observation : Set}
    (system : DualModeSemanticExecution
      Workload Authority BulkReceipt IncrementalReceipt Store)
    (observe : Authority → Observation)
    (workload : Workload) →
  observe (bulkCompile system workload)
    ≡ observe (incrementalCompile system workload)
consumerObservationAgreesAcrossModes system observe workload
  rewrite bulkAndIncrementalAuthoritiesAgree system workload = refl

------------------------------------------------------------------------
-- Anti-confusion boundary.
--
-- Exact semantic agreement does not imply that bulk and incremental execution
-- must expose the same physical receipt, scheduling granularity, transaction
-- pattern, staging carrier, or parallelism strategy.
------------------------------------------------------------------------

data SemanticEqualityForcesSamePhysicalPlanPermission : Set where

semanticEqualityDoesNotForceSamePhysicalPlan :
  SemanticEqualityForcesSamePhysicalPlanPermission → ⊥
semanticEqualityDoesNotForceSamePhysicalPlan ()
