module DASHI.Law.SensibLawUnifiedWorkbenchDioxusWgpuBridgeRegression where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Interop.DioxusWgpuHyperfabricBridgeExact as DioxusWgpu
import DASHI.Law.SensibLawUnifiedWorkbenchDioxusWgpuBridgeExact as Bridge
import DASHI.Law.SensibLawUnifiedWorkbenchProjectionExact as Workbench

boundaryExists : Set
boundaryExists = Bridge.UnifiedWorkbenchDioxusWgpuBoundary

canonicalBoundaryExists : boundaryExists
canonicalBoundaryExists = Bridge.canonicalUnifiedWorkbenchDioxusWgpuBoundary

matterProofMayRemainUnavailable :
  Workbench.availability Workbench.matterProofProjection
    ≡
  Workbench.unavailable
matterProofMayRemainUnavailable = Agda.Builtin.Equality.refl

shellGpuStillShareSelectionCommand :
  DioxusWgpu.decodeShell (DioxusWgpu.shellSelect DioxusWgpu.object42)
    ≡
  DioxusWgpu.decodeGpu (DioxusWgpu.gpuPick DioxusWgpu.object42)
shellGpuStillShareSelectionCommand = Bridge.dioxusGpuSelectionParity
