module DASHI.Interop.PortableInteractiveGpuProjectionRegression where

import DASHI.Interop.PortableInteractiveGpuProjectionExact as Generic
import DASHI.Interop.DioxusWgpuHyperfabricBridgeExact as Concrete
import DASHI.Interop.ITIRRibbonProjectionAuthorityBridgeExact as Ribbon

genericBoundaryPaid :
  Generic.PortableInteractiveGpuProjectionBoundary
genericBoundaryPaid =
  Generic.canonicalPortableInteractiveGpuProjectionBoundary

shellGpuCommandParityPaid :
  Concrete.decodeShell (Concrete.shellSelect Concrete.object42)
    ≡
  Concrete.decodeGpu (Concrete.gpuPick Concrete.object42)
shellGpuCommandParityPaid =
  Concrete.shellGpuSelect42CommandParity

shellGpuTransitionParityPaid :
  Concrete.step
    (Concrete.decodeShell (Concrete.shellSelect Concrete.object42))
    Concrete.initialState
    ≡
  Concrete.step
    (Concrete.decodeGpu (Concrete.gpuPick Concrete.object42))
    Concrete.initialState
shellGpuTransitionParityPaid =
  Concrete.shellGpuSelect42TransitionParity

ribbonProjectionAuthorityPaid :
  Ribbon.RibbonProjectionAuthorityBoundary
ribbonProjectionAuthorityPaid =
  Ribbon.canonicalRibbonProjectionAuthorityBoundary
