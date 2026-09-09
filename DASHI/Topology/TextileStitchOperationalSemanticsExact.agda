module DASHI.Topology.TextileStitchOperationalSemanticsExact where

open import DASHI.Core.Prelude

import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- Operational semantics for knitted and crocheted construction.
--
-- The carrier module intentionally permits arbitrary tagged StitchStep values.
-- This module closes that gap with mode-specific transition relations whose
-- constructors enforce the characteristic active-frontier update.
------------------------------------------------------------------------

data KnitTransition : Stitch.StitchState → Stitch.StitchState → Set where
  replaceLiveLoop :
    ∀ {loops anchors old new restFrontier} →
    KnitTransition
      (Stitch.stitch-state
        loops
        anchors
        (Stitch.active-loop-frontier (old ∷ restFrontier)))
      (Stitch.stitch-state
        (new ∷ loops)
        anchors
        (Stitch.active-loop-frontier (new ∷ restFrontier)))

knitTransitionToStep :
  ∀ {before after} →
  KnitTransition before after →
  Stitch.StitchStep
knitTransitionToStep
  (replaceLiveLoop
    {loops = loops}
    {anchors = anchors}
    {old = old}
    {new = new}
    {restFrontier = restFrontier}) =
  Stitch.stitch-step
    Stitch.knittingFormation
    (Stitch.stitch-state
      loops
      anchors
      (Stitch.active-loop-frontier (old ∷ restFrontier)))
    (Stitch.knitThrough old new)
    (Stitch.stitch-state
      (new ∷ loops)
      anchors
      (Stitch.active-loop-frontier (new ∷ restFrontier)))

record CrochetCompletedState : Set where
  constructor crochet-completed-state
  field
    fabricState : Stitch.StitchState
    workingLoop : Stitch.LoopId
    onlyWorkingLoopIsLive :
      Stitch.liveLoops (Stitch.frontier fabricState)
      ≡ workingLoop ∷ []

open CrochetCompletedState public

data CrochetTransition :
    CrochetCompletedState → CrochetCompletedState → Set where
  attachThroughAnchor :
    ∀ {loops anchors old new}
      (anchor : Stitch.AnchorId) →
    CrochetTransition
      (crochet-completed-state
        (Stitch.stitch-state
          loops
          anchors
          (Stitch.active-loop-frontier (old ∷ [])))
        old
        refl)
      (crochet-completed-state
        (Stitch.stitch-state
          (new ∷ loops)
          (anchor ∷ anchors)
          (Stitch.active-loop-frontier (new ∷ [])))
        new
        refl)

crochetTransitionToStep :
  ∀ {before after} →
  CrochetTransition before after →
  Stitch.StitchStep
crochetTransitionToStep
  (attachThroughAnchor
    {loops = loops}
    {anchors = anchors}
    {old = old}
    {new = new}
    anchor) =
  Stitch.stitch-step
    Stitch.crochetFormation
    (Stitch.stitch-state
      loops
      anchors
      (Stitch.active-loop-frontier (old ∷ [])))
    (Stitch.crochetThrough old anchor new)
    (Stitch.stitch-state
      (new ∷ loops)
      (anchor ∷ anchors)
      (Stitch.active-loop-frontier (new ∷ [])))

knittingFormationIsNotCrochetFormation :
  Stitch.knittingFormation ≡ Stitch.crochetFormation → ⊥
knittingFormationIsNotCrochetFormation ()

------------------------------------------------------------------------
-- The one-live-loop law above describes completed crochet macro-states.
-- Intermediate hook states for stitches that temporarily hold multiple loops
-- remain a separate micro-semantics coordinate and are not silently erased.
------------------------------------------------------------------------

data CompletedCrochetStateIsFullHookMicroSemantics : Set where

completedCrochetStateIsNotFullHookMicroSemantics :
  CompletedCrochetStateIsFullHookMicroSemantics → ⊥
completedCrochetStateIsNotFullHookMicroSemantics ()
