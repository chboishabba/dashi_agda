module DASHI.Law.SensibLawUnifiedWorkbenchInteractionIRBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Maybe using (just)

import DASHI.Core.PortableInteractiveViewExact as View
import DASHI.Interop.JesusCrustUIInteractionIRExact as Interaction
import DASHI.Interop.DioxusWgpuHyperfabricBridgeExact as DioxusWgpu
import DASHI.Interop.PortableInteractiveGpuProjectionExact as PortableGpu
import DASHI.Law.SensibLawUnifiedWorkbenchProjectionExact as Workbench

------------------------------------------------------------------------
-- M10 INTERFACE / INTERACTION IR WELD
--
-- The workbench UI is a semantic projection. PortableInteractiveViewExact
-- owns framework-neutral declarative controls; JesusCrustUIInteractionIRExact
-- owns intent-level interaction vocabulary; PortableInteractiveGpuProjection
-- owns shell/GPU proposal parity. Dioxus/wgpu are concrete interpreters only.
------------------------------------------------------------------------

selectActionTagExact :
  Interaction.actionKindTag Interaction.selectAction ≡ 3
selectActionTagExact = refl

focusActionTagExact :
  Interaction.actionKindTag Interaction.focusAction ≡ 2
focusActionTagExact = refl

followActionTagExact :
  Interaction.actionKindTag Interaction.followAction ≡ 6
followActionTagExact = refl

openSourceActionTagExact :
  Interaction.actionKindTag Interaction.openSourceAction ≡ 7
openSourceActionTagExact = refl

------------------------------------------------------------------------
-- Declarative interface specimen: activation emits the same domain command
-- language consumed by both shell and GPU projections.
------------------------------------------------------------------------

proofNodeButton :
  View.UiNode DioxusWgpu.DomainCommand
proofNodeButton =
  View.button
    "Select proof node"
    (DioxusWgpu.selectObject DioxusWgpu.object42)

proofNodeButtonActivation :
  View.activate proofNodeButton
    ≡ DioxusWgpu.selectObject DioxusWgpu.object42 ∷ []
proofNodeButtonActivation = refl

proofNodeBox :
  View.UiNode DioxusWgpu.DomainCommand
proofNodeBox =
  View.box
    (View.text "Proof/source object")
    (just (DioxusWgpu.focusProvenance DioxusWgpu.object42))

proofNodeBoxActivation :
  View.activate proofNodeBox
    ≡ DioxusWgpu.focusProvenance DioxusWgpu.object42 ∷ []
proofNodeBoxActivation = refl

------------------------------------------------------------------------
-- Shell and GPU interaction mechanisms refine to the same admitted commands.
------------------------------------------------------------------------

selectParity :
  DioxusWgpu.decodeShell
    (DioxusWgpu.shellSelect DioxusWgpu.object42)
  ≡
  DioxusWgpu.decodeGpu
    (DioxusWgpu.gpuPick DioxusWgpu.object42)
selectParity =
  DioxusWgpu.shellGpuSelect42CommandParity

focusParity :
  DioxusWgpu.decodeShell
    (DioxusWgpu.shellFocusProvenance DioxusWgpu.object42)
  ≡
  DioxusWgpu.decodeGpu
    (DioxusWgpu.gpuFocusProvenance DioxusWgpu.object42)
focusParity = refl

followParity :
  DioxusWgpu.decodeShell
    (DioxusWgpu.shellFollow DioxusWgpu.object42)
  ≡
  DioxusWgpu.decodeGpu
    (DioxusWgpu.gpuFollow DioxusWgpu.object42)
followParity = refl

------------------------------------------------------------------------
-- Parent contracts are reused, not restated.
------------------------------------------------------------------------

ViewBoundary : Set
ViewBoundary = View.PortableInteractiveViewBoundary

viewBoundaryPaid : ViewBoundary
viewBoundaryPaid = View.canonicalPortableInteractiveViewBoundary

GpuBoundary : Set
GpuBoundary = PortableGpu.PortableInteractiveGpuProjectionBoundary

gpuBoundaryPaid : GpuBoundary
gpuBoundaryPaid =
  PortableGpu.canonicalPortableInteractiveGpuProjectionBoundary

WorkbenchBoundary : Set
WorkbenchBoundary = Workbench.UnifiedWorkbenchBoundary

workbenchBoundaryPaid : WorkbenchBoundary
workbenchBoundaryPaid = Workbench.canonicalUnifiedWorkbenchBoundary

InteractionWireBoundary : Set
InteractionWireBoundary = Interaction.UIInteractionWireParity

interactionWireBoundaryPaid : InteractionWireBoundary
interactionWireBoundaryPaid = Interaction.canonicalUIInteractionWireParity

------------------------------------------------------------------------
-- Workbench-specific firewalls.
------------------------------------------------------------------------

data PhysicalGestureBecomesCanonicalIntent : Set where
data CssSelectorBecomesCanonicalTarget : Set where
data UiActivationCreatesSemanticAuthority : Set where
data InteractionObservationCreatesClaimTruth : Set where
data VisualPickPaysLegalResidual : Set where
data HiddenVisualObjectAbsentFromWorld : Set where

physicalGestureNotCanonicalIntent :
  PhysicalGestureBecomesCanonicalIntent → ⊥
physicalGestureNotCanonicalIntent ()

cssSelectorNotCanonicalTarget :
  CssSelectorBecomesCanonicalTarget → ⊥
cssSelectorNotCanonicalTarget ()

uiActivationDoesNotCreateAuthority :
  UiActivationCreatesSemanticAuthority → ⊥
uiActivationDoesNotCreateAuthority ()

interactionObservationDoesNotCreateTruth :
  InteractionObservationCreatesClaimTruth → ⊥
interactionObservationDoesNotCreateTruth ()

visualPickDoesNotPayResidual :
  VisualPickPaysLegalResidual → ⊥
visualPickDoesNotPayResidual ()

hiddenVisualObjectStillExistsSemantically :
  HiddenVisualObjectAbsentFromWorld → ⊥
hiddenVisualObjectStillExistsSemantically ()

record UnifiedWorkbenchInteractionIRBoundary : Set where
  constructor unifiedWorkbenchInteractionIRBoundary
  field
    interfaceIrOwnsDeclarativeControls : Bool
    interfaceIrOwnsDeclarativeControlsIsTrue :
      interfaceIrOwnsDeclarativeControls ≡ true

    interactionIrOwnsIntentVocabulary : Bool
    interactionIrOwnsIntentVocabularyIsTrue :
      interactionIrOwnsIntentVocabulary ≡ true

    shellAndGpuRefineSameCommandLanguage : Bool
    shellAndGpuRefineSameCommandLanguageIsTrue :
      shellAndGpuRefineSameCommandLanguage ≡ true

    physicalGestureIsCanonicalIntent : Bool
    physicalGestureIsCanonicalIntentIsFalse :
      physicalGestureIsCanonicalIntent ≡ false

    cssSelectorIsCanonicalTarget : Bool
    cssSelectorIsCanonicalTargetIsFalse :
      cssSelectorIsCanonicalTarget ≡ false

    interactionCreatesSemanticAuthority : Bool
    interactionCreatesSemanticAuthorityIsFalse :
      interactionCreatesSemanticAuthority ≡ false

    interactionCreatesClaimTruth : Bool
    interactionCreatesClaimTruthIsFalse :
      interactionCreatesClaimTruth ≡ false

    interactionPaysResidual : Bool
    interactionPaysResidualIsFalse :
      interactionPaysResidual ≡ false

open UnifiedWorkbenchInteractionIRBoundary public

canonicalUnifiedWorkbenchInteractionIRBoundary :
  UnifiedWorkbenchInteractionIRBoundary
canonicalUnifiedWorkbenchInteractionIRBoundary =
  unifiedWorkbenchInteractionIRBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
