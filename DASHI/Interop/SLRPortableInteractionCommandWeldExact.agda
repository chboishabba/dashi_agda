module DASHI.Interop.SLRPortableInteractionCommandWeldExact where

open import DASHI.Core.Prelude
open import Data.Maybe using (Maybe; just; nothing)

import DASHI.Interop.JesusCrustUIInteractionIRExact as UI
import DASHI.Interop.SemanticReaderElucidatoryConeExact as Reader
import DASHI.Interop.PortableInteractiveGpuProjectionExact as Portable
import DASHI.Interop.DioxusWgpuHyperfabricBridgeExact as DioxusWgpu

------------------------------------------------------------------------
-- SLR MATTER-COMMAND KIND WELD
--
-- Existing UI action tags and semantic-reader intents remain their own
-- source-level vocabularies.  This owner identifies only the shared admitted
-- command roles needed by the production MatterRuntime boundary.
------------------------------------------------------------------------

data MatterCommandKind : Set where
  selectObjectKind : MatterCommandKind
  followTargetKind : MatterCommandKind
  focusProvenanceKind : MatterCommandKind
  openSourceKind : MatterCommandKind
  explainKind : MatterCommandKind
  expandExplanationKind : MatterCommandKind
  backKind : MatterCommandKind

uiActionCommandKind : UI.ActionKind → Maybe MatterCommandKind
uiActionCommandKind UI.selectAction = just selectObjectKind
uiActionCommandKind UI.followAction = just followTargetKind
uiActionCommandKind UI.focusAction = just focusProvenanceKind
uiActionCommandKind UI.openSourceAction = just openSourceKind
uiActionCommandKind UI.expandAction = just expandExplanationKind
uiActionCommandKind UI.activateAction = nothing
uiActionCommandKind UI.collapseAction = nothing
uiActionCommandKind UI.zoomAction = nothing

readerIntentCommandKind : Reader.SemanticIntent → Maybe MatterCommandKind
readerIntentCommandKind Reader.openSourceIntent = just openSourceKind
readerIntentCommandKind Reader.followReferenceIntent = just followTargetKind
readerIntentCommandKind Reader.expandProofConeIntent = just expandExplanationKind
readerIntentCommandKind Reader.whyClaimIntent = just explainKind
readerIntentCommandKind Reader.explainSpanIntent = just explainKind
readerIntentCommandKind Reader.explainRoleIntent = just explainKind
readerIntentCommandKind Reader.backIntent = just backKind
readerIntentCommandKind Reader.exploreEntityIntent = just followTargetKind

uiReaderOpenSourceKindParity :
  uiActionCommandKind UI.openSourceAction
    ≡
  readerIntentCommandKind Reader.openSourceIntent
uiReaderOpenSourceKindParity = refl

uiReaderFollowKindParity :
  uiActionCommandKind UI.followAction
    ≡
  readerIntentCommandKind Reader.followReferenceIntent
uiReaderFollowKindParity = refl

uiReaderExpandKindParity :
  uiActionCommandKind UI.expandAction
    ≡
  readerIntentCommandKind Reader.expandProofConeIntent
uiReaderExpandKindParity = refl

------------------------------------------------------------------------
-- The v0 shell/GPU bridge already inhabits SelectObject.  This witness records
-- its role in the broader MatterCommand family without claiming GPU inputs
-- must exist for every reader-only command.
------------------------------------------------------------------------

dioxusWgpuSelectRole :
  MatterCommandKind
dioxusWgpuSelectRole = selectObjectKind

shellSelect42IsSelectObjectKind :
  dioxusWgpuSelectRole ≡ selectObjectKind
shellSelect42IsSelectObjectKind = refl

gpuPick42SharesShellCommand :
  DioxusWgpu.decodeGpu (DioxusWgpu.gpuPick DioxusWgpu.object42)
    ≡
  DioxusWgpu.decodeShell (DioxusWgpu.shellSelect DioxusWgpu.object42)
gpuPick42SharesShellCommand = refl

------------------------------------------------------------------------
-- Authority remains inherited from the portable interaction owner.
------------------------------------------------------------------------

PortableBoundary : Set
PortableBoundary = Portable.PortableInteractiveGpuProjectionBoundary

portableBoundaryPaid : PortableBoundary
portableBoundaryPaid =
  Portable.canonicalPortableInteractiveGpuProjectionBoundary
