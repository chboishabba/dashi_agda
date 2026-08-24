{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.WholeTrancheExecutionArchitectureExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.DualModeSemanticExecutionExact as Dual
import DASHI.Cognition.PNF.HierarchicalDeltaFusionExact as Delta
import DASHI.Cognition.PNF.IndependentFibreBatchExecutionExact as Batch
import DASHI.Cognition.PNF.ReusableTemplateTrancheEconomyExact as Reuse

------------------------------------------------------------------------
-- WHOLE-TRANCHE EXECUTION CONSTITUTION
--
-- This composes the previously separate local laws into one architecture:
--
--   parser numeric stream
--     -> local semantic deltas
--     -> lawful batch/fibre execution
--     -> hierarchical delta promotion
--     -> reusable compiled structure
--     -> shared authority publication
--
-- Bulk bootstrap and sparse incremental execution may use different physical
-- plans, but both must implement the same authority.  Cost optimization begins
-- only after these semantic obligations are inhabited.
------------------------------------------------------------------------

record WholeTrancheExecutionArchitecture
  (Workload Authority BulkReceipt IncrementalReceipt Store
   ChildState DeltaState ParentState
   BatchInput BatchAuthority BatchReceipt
   TemplateInput Template TemplateAuthority Work : Set)
  (LeqWork : Work → Work → Set)
  : Set₂ where
  field
    dualMode :
      Dual.DualModeSemanticExecution
        Workload Authority BulkReceipt IncrementalReceipt Store

    hierarchy :
      Delta.HierarchicalDeltaStep ChildState DeltaState ParentState

    batch :
      Batch.ExactBatchRealization BatchInput BatchAuthority BatchReceipt

    reuse :
      Reuse.ReusableCompiledTemplate
        TemplateInput Template TemplateAuthority Work LeqWork

open WholeTrancheExecutionArchitecture public

------------------------------------------------------------------------
-- The architecture does NOT identify these proof obligations with one another.
-- Exact batching does not prove reusable-template admissibility; reuse does not
-- prove hierarchy locality; and semantic dual-mode equality does not prove a
-- physical speedup.  They are composed, not conflated.
------------------------------------------------------------------------

data SemanticExactnessImpliesPerformanceWinPermission : Set where

data BatchExactnessImpliesReuseAdmissibilityPermission : Set where

data HierarchyImpliesParallelIndependencePermission : Set where

semanticExactnessDoesNotManufacturePerformanceWin :
  SemanticExactnessImpliesPerformanceWinPermission → ⊥
semanticExactnessDoesNotManufacturePerformanceWin ()

batchExactnessDoesNotManufactureReuseAdmissibility :
  BatchExactnessImpliesReuseAdmissibilityPermission → ⊥
batchExactnessDoesNotManufactureReuseAdmissibility ()

hierarchyDoesNotManufactureParallelIndependence :
  HierarchyImpliesParallelIndependencePermission → ⊥
hierarchyDoesNotManufactureParallelIndependence ()

------------------------------------------------------------------------
-- ANTI-CARTESIAN PRINCIPLE
--
-- The desired execution architecture is support/fibre driven.  A broad
-- candidate cross product may still be used as a specification/reference
-- relation, but it is not a required physical carrier.  Any implementation that
-- replaces it must prove the relevant exactness theorem before cost is compared.
------------------------------------------------------------------------

data SpecificationRelationRequiresPhysicalCartesianProductPermission : Set where

specificationRelationDoesNotRequirePhysicalCartesianProduct :
  SpecificationRelationRequiresPhysicalCartesianProductPermission → ⊥
specificationRelationDoesNotRequirePhysicalCartesianProduct ()
