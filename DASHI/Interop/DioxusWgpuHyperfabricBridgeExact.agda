module DASHI.Interop.DioxusWgpuHyperfabricBridgeExact where

open import DASHI.Core.Prelude
open import Data.Maybe using (Maybe; just; nothing)
import DASHI.Interop.PortableInteractiveGpuProjectionExact as Interactive

------------------------------------------------------------------------
-- CONCRETE V0 DIOXUS / WGPU COMMAND-PARITY FIXTURE
--
-- Technology names identify interpreter roles only.  Neither the shell nor
-- the GPU lane is semantic authority.
------------------------------------------------------------------------

data VisualObjectId : Set where
  object7 : VisualObjectId
  object42 : VisualObjectId

data DomainCommand : Set where
  selectObject : VisualObjectId → DomainCommand
  followTarget : VisualObjectId → DomainCommand
  focusProvenance : VisualObjectId → DomainCommand

record SemanticState : Set where
  constructor semanticState
  field
    selected : Maybe VisualObjectId

open SemanticState public

data ShellInput : Set where
  shellSelect : VisualObjectId → ShellInput
  shellFollow : VisualObjectId → ShellInput
  shellFocusProvenance : VisualObjectId → ShellInput

data GpuInput : Set where
  gpuPick : VisualObjectId → GpuInput
  gpuFollow : VisualObjectId → GpuInput
  gpuFocusProvenance : VisualObjectId → GpuInput

data ShellProjection : Set where
  shellNothingSelected : ShellProjection
  shellSelected : VisualObjectId → ShellProjection

data VisualProjection : Set where
  visualNothingSelected : VisualProjection
  visualSelected : VisualObjectId → VisualProjection

projectShell : SemanticState → ShellProjection
projectShell (semanticState nothing) = shellNothingSelected
projectShell (semanticState (just id)) = shellSelected id

projectVisual : SemanticState → VisualProjection
projectVisual (semanticState nothing) = visualNothingSelected
projectVisual (semanticState (just id)) = visualSelected id

decodeShell : ShellInput → DomainCommand
decodeShell (shellSelect id) = selectObject id
decodeShell (shellFollow id) = followTarget id
decodeShell (shellFocusProvenance id) = focusProvenance id

decodeGpu : GpuInput → DomainCommand
decodeGpu (gpuPick id) = selectObject id
decodeGpu (gpuFollow id) = followTarget id
decodeGpu (gpuFocusProvenance id) = focusProvenance id

step : DomainCommand → SemanticState → SemanticState
step (selectObject id) _ = semanticState (just id)
step (followTarget id) _ = semanticState (just id)
step (focusProvenance id) state = state

owner : Interactive.PortableInteractiveGpuProjection
owner =
  Interactive.portableInteractiveGpuProjection
    SemanticState
    DomainCommand
    ShellProjection
    VisualProjection
    ShellInput
    GpuInput
    projectShell
    projectVisual
    decodeShell
    decodeGpu
    step

shellSelect42Decodes :
  decodeShell (shellSelect object42) ≡ selectObject object42
shellSelect42Decodes = refl

gpuPick42Decodes :
  decodeGpu (gpuPick object42) ≡ selectObject object42
gpuPick42Decodes = refl

shellGpuSelect42CommandParity :
  decodeShell (shellSelect object42)
    ≡
  decodeGpu (gpuPick object42)
shellGpuSelect42CommandParity = refl

initialState : SemanticState
initialState = semanticState nothing

shellGpuSelect42TransitionParity :
  step (decodeShell (shellSelect object42)) initialState
    ≡
  step (decodeGpu (gpuPick object42)) initialState
shellGpuSelect42TransitionParity =
  Interactive.sameDecodedCommandSameTransition
    {owner = owner}
    {state = initialState}
    {shellInput = shellSelect object42}
    {gpuInput = gpuPick object42}
    shellGpuSelect42CommandParity

selected42AfterShell :
  step (decodeShell (shellSelect object42)) initialState
    ≡
  semanticState (just object42)
selected42AfterShell = refl

selected42AfterGpu :
  step (decodeGpu (gpuPick object42)) initialState
    ≡
  semanticState (just object42)
selected42AfterGpu = refl

------------------------------------------------------------------------
-- The concrete bridge retains the generic firewalls unchanged.
------------------------------------------------------------------------

ConcreteBoundary : Set
ConcreteBoundary = Interactive.PortableInteractiveGpuProjectionBoundary

concreteBoundaryPaid : ConcreteBoundary
concreteBoundaryPaid =
  Interactive.canonicalPortableInteractiveGpuProjectionBoundary
