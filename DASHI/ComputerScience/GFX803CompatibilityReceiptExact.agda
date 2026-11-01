module DASHI.ComputerScience.GFX803CompatibilityReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.ComputerScience.CUDAROCmExecutionBackendFibreExact as Backend
import DASHI.ComputerScience.GPUCompatibilityObservationExact as Compat

------------------------------------------------------------------------
-- GFX803 / POLARIS PROJECT-BOUND COMPATIBILITY RECEIPT
--
-- This is a thin adapter over the generic compatibility calculus.  It records
-- what the gfx803 compatibility workspace claims as project evidence; it does
-- not turn those observations into AMD guarantees or universal ROCm claims.
------------------------------------------------------------------------

record GFX803ProjectReceipt : Set where
  constructor gfx803-project-receipt
  field
    projectReference : String
    hardwareFamily : String
    backend : Backend.GPUBackendKind
    runtimeLane : String
    workloadSurface : String
    querySurface : String
    retainedArtifactReference : String
    projectBound : Bool
    vendorGuaranteeCreated : Bool
    universalROCmClaimCreated : Bool
open GFX803ProjectReceipt public

oldABICompatibilityReceipt : GFX803ProjectReceipt
oldABICompatibilityReceipt =
  gfx803-project-receipt
    "chboishabba/gfx803_compat_graph"
    "AMD Polaris / gfx803"
    Backend.rocmHIPBackend
    "preserved old HSA/HIP ABI with selected newer support libraries"
    "PyTorch / ROCm host compatibility"
    "GPU visibility and bounded runtime compatibility"
    "repo benchmark / runtime receipts"
    true false false

leechCorrectnessReceipt : GFX803ProjectReceipt
leechCorrectnessReceipt =
  gfx803-project-receipt
    "chboishabba/gfx803_compat_graph"
    "AMD Polaris / gfx803"
    Backend.rocmHIPBackend
    "extracted ROCm 5.7 / 6.4 diagnostic lanes"
    "LeechTransformer"
    "numerical correctness / repeated-run determinism"
    "retained probe and drift artifacts"
    true false false

whisperXResetSafetyReceipt : GFX803ProjectReceipt
whisperXResetSafetyReceipt =
  gfx803-project-receipt
    "chboishabba/gfx803_compat_graph"
    "AMD Polaris / gfx803"
    Backend.rocmHIPBackend
    "extracted ROCm 6.4 host lane"
    "WhisperX"
    "long async workload reset safety"
    "profiler, heartbeat, observer and kernel-reset evidence"
    true false false

------------------------------------------------------------------------
-- Cross-pollination with the generic exact witnesses.
------------------------------------------------------------------------

visibilityCorrectnessDefect : Compat.VisibilityCorrectnessDefect
visibilityCorrectnessDefect = Compat.visibilityCorrectnessDefect

summaryResetSafetyDefect : Compat.SummaryResetSafetyDefect
summaryResetSafetyDefect = Compat.summaryResetSafetyDefect

oldAbiUpgradeCounterexample : Compat.UpgradeCounterexample
oldAbiUpgradeCounterexample = Compat.canonicalUpgradeCounterexample

blockingMitigationReceipt : Compat.InterventionReceipt
blockingMitigationReceipt = Compat.blockingMitigationReceipt

record GFX803Boundary : Set where
  constructor gfx803-boundary
  field
    compatibilityIsQueryIndexed : Bool
    gpuVisibilityImpliesNumericalCorrectness : Bool
    shortSuccessImpliesLongAsyncResetSafety : Bool
    oldABIPreservationIsScopedCompatibilityEvidence : Bool
    latestComponentsAreAutomaticallyBetterOnPolaris : Bool
    blockingSuccessProvesAsyncSchedulingRootCause : Bool
    projectReceiptCreatesVendorGuarantee : Bool
    retainedRuntimeEvidenceIsPhysicalFormalProof : Bool
open GFX803Boundary public

canonicalGFX803Boundary : GFX803Boundary
canonicalGFX803Boundary =
  gfx803-boundary
    true
    false
    false
    true
    false
    false
    false
    false
