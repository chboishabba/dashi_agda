{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.WorkloadOptimizationAdmissionExact where

open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Empty using (⊥)
open import DASHI.Cognition.PNF.ComplexityArithmetic using (_≤ᶜ_)

------------------------------------------------------------------------
-- Workload-fit optimization admission.
--
-- Cross-repo design evidence:
--   chboishabba/dashitest/swar_test_harness.py
--   chboishabba/dashitest/packing_ablation_bench.py
--   chboishabba/dashiCORE/pq.py
--
-- Those implementations distinguish persistent packed/native execution from
-- repeated packing/unpacking and keep packed representation observationally
-- invisible to semantics.  This module extracts only the reusable admission
-- rule: semantic equality is mandatory, boundary/setup cost is part of the
-- measured candidate, and theoretical inner-kernel throughput cannot promote
-- an unsuitable backend by itself.
------------------------------------------------------------------------

data BackendFamily : Set where
  packedScalar
  batchVector
  nativeSWAR
  accelerator : BackendFamily

record WorkloadGeometry : Set where
  constructor workloadGeometry
  field
    itemCount : Nat
    meanFibreItemsCode : Nat
    usefulOperationCount : Nat
    homogeneous : Set
    alreadyCandidateNative : Set
    repackingRequired : Set

open WorkloadGeometry public

record BackendMeasurement : Set where
  constructor backendMeasurement
  field
    family : BackendFamily
    setupWork : Nat
    repackWork : Nat
    dispatchWork : Nat
    transferWork : Nat
    kernelWork : Nat
    totalWork : Nat
    accountedNoMoreThanTotal :
      setupWork + repackWork + dispatchWork + transferWork + kernelWork ≤ᶜ totalWork

open BackendMeasurement public

boundaryWork : BackendMeasurement → Nat
boundaryWork m =
  setupWork m + repackWork m + dispatchWork m + transferWork m

------------------------------------------------------------------------
-- Geometry is a caller-supplied proof obligation because no universal token,
-- batch-size, or arithmetic-intensity threshold is asserted.  The same
-- backend can be appropriate for one workload and inappropriate for another.
------------------------------------------------------------------------

record OptimizationAdmission
    (geometry : WorkloadGeometry)
    (reference candidate : BackendMeasurement) : Set₁ where
  constructor optimizationAdmission
  field
    authorityExact : Set
    geometryAppropriate : Set
    totalNoWorse : totalWork candidate ≤ᶜ totalWork reference
    strictTotalWin : suc (totalWork candidate) ≤ᶜ totalWork reference

open OptimizationAdmission public

------------------------------------------------------------------------
-- Fail-closed boundaries: no Ferrari-by-name admission.
------------------------------------------------------------------------

data HigherTheoreticalThroughputImpliesPromotion : Set where

data MorePackedRepresentationImpliesPromotion : Set where

data MoreParallelBackendImpliesPromotion : Set where

data FasterInnerKernelCanIgnoreBoundaryWork : Set where

data SemanticParityAloneImpliesPromotion : Set where

theoreticalThroughputDoesNotPromote :
  HigherTheoreticalThroughputImpliesPromotion → ⊥
theoreticalThroughputDoesNotPromote ()

packingDoesNotPromote : MorePackedRepresentationImpliesPromotion → ⊥
packingDoesNotPromote ()

parallelismDoesNotPromote : MoreParallelBackendImpliesPromotion → ⊥
parallelismDoesNotPromote ()

innerKernelCannotHideBoundaryWork : FasterInnerKernelCanIgnoreBoundaryWork → ⊥
innerKernelCannotHideBoundaryWork ()

parityIsNecessaryNotSufficient : SemanticParityAloneImpliesPromotion → ⊥
parityIsNecessaryNotSufficient ()
