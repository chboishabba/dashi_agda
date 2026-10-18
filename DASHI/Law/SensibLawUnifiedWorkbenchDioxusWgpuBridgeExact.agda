module DASHI.Law.SensibLawUnifiedWorkbenchDioxusWgpuBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.DioxusWgpuHyperfabricBridgeExact as DioxusWgpu
import DASHI.Interop.PortableInteractiveGpuProjectionExact as PortableGpu
import DASHI.Law.SensibLawUnifiedWorkbenchProjectionExact as Workbench

------------------------------------------------------------------------
-- M10 DIOXUS/WGPU UNIFIED WORKBENCH BRIDGE
--
-- The workbench projection and the Dioxus/wgpu interaction interpreter are
-- sibling refinements of one canonical semantic state.  Changing projection
-- depth affects visibility only; shell/GPU interaction acquires semantic force
-- only after decoding to the same domain command and entering the same reducer.
------------------------------------------------------------------------

WorkbenchBoundary : Set
WorkbenchBoundary = Workbench.UnifiedWorkbenchBoundary

workbenchBoundaryPaid : WorkbenchBoundary
workbenchBoundaryPaid = Workbench.canonicalUnifiedWorkbenchBoundary

InteractiveBoundary : Set
InteractiveBoundary = PortableGpu.PortableInteractiveGpuProjectionBoundary

interactiveBoundaryPaid : InteractiveBoundary
interactiveBoundaryPaid =
  PortableGpu.canonicalPortableInteractiveGpuProjectionBoundary

dioxusGpuSelectionParity :
  DioxusWgpu.decodeShell (DioxusWgpu.shellSelect DioxusWgpu.object42)
    ≡
  DioxusWgpu.decodeGpu (DioxusWgpu.gpuPick DioxusWgpu.object42)
dioxusGpuSelectionParity = DioxusWgpu.shellGpuSelect42CommandParity

dioxusGpuTransitionParity :
  DioxusWgpu.step
    (DioxusWgpu.decodeShell (DioxusWgpu.shellSelect DioxusWgpu.object42))
    DioxusWgpu.initialState
  ≡
  DioxusWgpu.step
    (DioxusWgpu.decodeGpu (DioxusWgpu.gpuPick DioxusWgpu.object42))
    DioxusWgpu.initialState
dioxusGpuTransitionParity = DioxusWgpu.shellGpuSelect42TransitionParity

record UnifiedWorkbenchDioxusWgpuBoundary : Set where
  constructor unifiedWorkbenchDioxusWgpuBoundary
  field
    dioxusIsProjectionNotAuthority : Bool
    dioxusIsProjectionNotAuthorityIsTrue :
      dioxusIsProjectionNotAuthority ≡ true

    wgpuIsProjectionNotAuthority : Bool
    wgpuIsProjectionNotAuthorityIsTrue :
      wgpuIsProjectionNotAuthority ≡ true

    shellAndGpuShareDomainCommand : Bool
    shellAndGpuShareDomainCommandIsTrue :
      shellAndGpuShareDomainCommand ≡ true

    stageAvailabilityMayRemainUnavailable : Bool
    stageAvailabilityMayRemainUnavailableIsTrue :
      stageAvailabilityMayRemainUnavailable ≡ true

    projectionChangeCreatesSemanticAuthority : Bool
    projectionChangeCreatesSemanticAuthorityIsFalse :
      projectionChangeCreatesSemanticAuthority ≡ false

    projectionChangeCreatesClaimTruth : Bool
    projectionChangeCreatesClaimTruthIsFalse :
      projectionChangeCreatesClaimTruth ≡ false

    projectionChangePaysResidual : Bool
    projectionChangePaysResidualIsFalse :
      projectionChangePaysResidual ≡ false

    gpuPickCreatesSemanticAuthority : Bool
    gpuPickCreatesSemanticAuthorityIsFalse :
      gpuPickCreatesSemanticAuthority ≡ false

canonicalUnifiedWorkbenchDioxusWgpuBoundary :
  UnifiedWorkbenchDioxusWgpuBoundary
canonicalUnifiedWorkbenchDioxusWgpuBoundary =
  unifiedWorkbenchDioxusWgpuBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
