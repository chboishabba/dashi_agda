module DASHI.Topology.TextileStitchHyperfabricExact where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)

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

data StitchOperation : Set where
  knitThrough : LoopId → LoopId → StitchOperation
  crochetThrough : LoopId → AnchorId → LoopId → StitchOperation
  bindLoops : LoopId → LoopId → LoopId → StitchOperation
  releaseLoop : LoopId → StitchOperation

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

record SameFinalObservation
    (first second : RealisedStitchHyperfabric) : Set where
  constructor same-final-observation
  field
    finalStatesAgree : finalState first ≡ finalState second

open SameFinalObservation public
