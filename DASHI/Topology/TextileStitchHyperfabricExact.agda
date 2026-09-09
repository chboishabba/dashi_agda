module DASHI.Topology.TextileStitchHyperfabricExact where

------------------------------------------------------------------------
-- Neutral loop/stitch topology for knitting and crochet.
--
-- This module does not identify weave crossings with loop stitches.  It owns
-- only the common loop/anchor/frontier vocabulary needed to give knitting and
-- crochet separate operational sublanguages over one stitch-hyperfabric.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)

record LoopId : Set where
  constructor loop-id
  field
    loopIndex : Nat

record AnchorId : Set where
  constructor anchor-id
  field
    anchorIndex : Nat

open LoopId public
open AnchorId public

record ActiveLoopFrontier : Set where
  constructor active-loop-frontier
  field
    liveLoops : List LoopId

open ActiveLoopFrontier public

data FormationMode : Set where
  knittingFormation : FormationMode
  crochetFormation : FormationMode

------------------------------------------------------------------------
-- Topological operations.
--
-- knitThrough records a new loop formed through an existing loop.
-- crochetThrough records the distinguished active loop and its anchor.
-- bindLoops supports join/decrease-like local topology without assigning a
-- named real-world stitch until a source-specific operational instance does so.
------------------------------------------------------------------------

data StitchOperation : Set where
  knitThrough :
    LoopId → LoopId → StitchOperation

  crochetThrough :
    LoopId → AnchorId → LoopId → StitchOperation

  bindLoops :
    LoopId → LoopId → LoopId → StitchOperation

  releaseLoop :
    LoopId → StitchOperation

record StitchState : Set where
  constructor stitch-state
  field
    loops : List LoopId
    anchors : List AnchorId
    frontier : ActiveLoopFrontier

open StitchState public

record StitchStep : Set where
  constructor stitch-step
  field
    mode : FormationMode
    before : StitchState
    operation : StitchOperation
    after : StitchState

open StitchStep public

StitchProgram : Set
StitchProgram = List StitchStep

------------------------------------------------------------------------
-- Construction history is deliberately retained separately from final state.
------------------------------------------------------------------------

record RealisedStitchHyperfabric : Set where
  constructor realised-stitch-hyperfabric
  field
    initialState : StitchState
    constructionHistory : StitchProgram
    finalState : StitchState

open RealisedStitchHyperfabric public

record KnitStepWitness (step : StitchStep) : Set where
  constructor knit-step-witness
  field
    isKnitting : mode step ≡ knittingFormation

record CrochetStepWitness (step : StitchStep) : Set where
  constructor crochet-step-witness
  field
    isCrochet : mode step ≡ crochetFormation

------------------------------------------------------------------------
-- Non-collapse boundary: the same final state does not erase construction
-- history or formation mode.  Equality of final states is only an observation.
------------------------------------------------------------------------

record SameFinalObservation
    (first second : RealisedStitchHyperfabric) : Set where
  constructor same-final-observation
  field
    finalStatesAgree : finalState first ≡ finalState second

open SameFinalObservation public
