module DASHI.Interop.JesusCrustUIInteractionIRExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Exact cross-language contract for the JesusCrust UI interaction IR.
-- This is intent-level UI flow, not DOM patch syntax or physical gestures.
------------------------------------------------------------------------

data TargetKind : Set where
  semanticTarget : TargetKind
  sourceTarget : TargetKind

targetKindTag : TargetKind → Nat
targetKindTag semanticTarget = 1
targetKindTag sourceTarget = 2

data StepKind : Set where
  actStep : StepKind
  expectStep : StepKind

stepKindTag : StepKind → Nat
stepKindTag actStep = 1
stepKindTag expectStep = 2

data ActionKind : Set where
  activateAction : ActionKind
  focusAction : ActionKind
  selectAction : ActionKind
  expandAction : ActionKind
  collapseAction : ActionKind
  followAction : ActionKind
  openSourceAction : ActionKind
  zoomAction : ActionKind

actionKindTag : ActionKind → Nat
actionKindTag activateAction = 1
actionKindTag focusAction = 2
actionKindTag selectAction = 3
actionKindTag expandAction = 4
actionKindTag collapseAction = 5
actionKindTag followAction = 6
actionKindTag openSourceAction = 7
actionKindTag zoomAction = 8

data ObservationKind : Set where
  visibleObservation : ObservationKind
  hiddenObservation : ObservationKind
  focusedObservation : ObservationKind
  selectedObservation : ObservationKind
  expandedObservation : ObservationKind
  collapsedObservation : ObservationKind

observationKindTag : ObservationKind → Nat
observationKindTag visibleObservation = 1
observationKindTag hiddenObservation = 2
observationKindTag focusedObservation = 3
observationKindTag selectedObservation = 4
observationKindTag expandedObservation = 5
observationKindTag collapsedObservation = 6

data ZoomLevel : Set where
  zoomIn : ZoomLevel
  zoomOut : ZoomLevel
  zoomFit : ZoomLevel

zoomLevelDetailTag : ZoomLevel → Nat
zoomLevelDetailTag zoomIn = 1
zoomLevelDetailTag zoomOut = 2
zoomLevelDetailTag zoomFit = 3

wireVersion : Nat
wireVersion = 1

maxProgramSteps : Nat
maxProgramSteps = 1048576

maxTargetBytes : Nat
maxTargetBytes = 1048576

record WorkSignature : Set where
  constructor workSignature
  field
    targetResolutions : Nat
    stateReads : Nat
    stateWrites : Nat
    commitBoundaries : Nat
    externalIO : Nat

open WorkSignature public

localActionWork : WorkSignature
localActionWork = workSignature 1 0 1 1 0

externalActionWork : WorkSignature
externalActionWork = workSignature 1 0 1 1 1

observationWork : WorkSignature
observationWork = workSignature 1 1 0 0 0

actionWork : ActionKind → WorkSignature
actionWork followAction = externalActionWork
actionWork openSourceAction = externalActionWork
actionWork _ = localActionWork

record UIInteractionWireParity : Set where
  constructor uiInteractionWireParity
  field
    magicIsJCUI : Bool
    versionIsOne : Bool
    littleEndianHeader : Bool
    explicitU32StepCount : Bool
    stepCountBoundedBeforeAllocation : Bool
    maxStepsIs1048576 : Bool
    explicitU32TargetLength : Bool
    targetLengthBoundedBeforeDecode : Bool
    maxTargetBytesIs1048576 : Bool
    targetKindsExact : Bool
    stepKindsExact : Bool
    actionTagsExact : Bool
    observationTagsExact : Bool
    zoomDetailTagsExact : Bool
    targetTextIsUtf8 : Bool
    jsonTransportUsed : Bool
    regexFlowParserUsed : Bool
    cssSelectorIsCanonicalTarget : Bool
    physicalGestureIsCanonicalIntent : Bool
    interactionReceiptCreatesBelief : Bool
    interactionReceiptCreatesUnderstanding : Bool
    interactionReceiptCreatesSemanticTruth : Bool
    interactionReceiptCreatesLegalTruth : Bool

open UIInteractionWireParity public

canonicalUIInteractionWireParity : UIInteractionWireParity
canonicalUIInteractionWireParity =
  uiInteractionWireParity
    true true true true true true
    true true true
    true true true true true true
    false false false false
    false false false false

------------------------------------------------------------------------
-- Firewalls: interaction telemetry remains observation, never epistemic truth.
------------------------------------------------------------------------

data JsonUIFlowTransport : Set where
data RegexUIFlowParser : Set where
data CanonicalCssSelectorTarget : Set where
data CanonicalPhysicalGestureIntent : Set where
data InteractionReceiptCreatesBelief : Set where
data InteractionReceiptCreatesUnderstanding : Set where
data InteractionReceiptCreatesSemanticTruth : Set where
data InteractionReceiptCreatesLegalTruth : Set where

jsonUIFlowTransportForbidden : JsonUIFlowTransport → ⊥
jsonUIFlowTransportForbidden ()

regexUIFlowParserForbidden : RegexUIFlowParser → ⊥
regexUIFlowParserForbidden ()

cssSelectorNotCanonicalTarget : CanonicalCssSelectorTarget → ⊥
cssSelectorNotCanonicalTarget ()

physicalGestureNotCanonicalIntent : CanonicalPhysicalGestureIntent → ⊥
physicalGestureNotCanonicalIntent ()

interactionReceiptDoesNotCreateBelief : InteractionReceiptCreatesBelief → ⊥
interactionReceiptDoesNotCreateBelief ()

interactionReceiptDoesNotCreateUnderstanding : InteractionReceiptCreatesUnderstanding → ⊥
interactionReceiptDoesNotCreateUnderstanding ()

interactionReceiptDoesNotCreateSemanticTruth : InteractionReceiptCreatesSemanticTruth → ⊥
interactionReceiptDoesNotCreateSemanticTruth ()

interactionReceiptDoesNotCreateLegalTruth : InteractionReceiptCreatesLegalTruth → ⊥
interactionReceiptDoesNotCreateLegalTruth ()
