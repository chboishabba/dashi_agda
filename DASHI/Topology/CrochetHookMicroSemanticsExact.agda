module DASHI.Topology.CrochetHookMicroSemanticsExact where

open import DASHI.Core.Prelude

import DASHI.Topology.TextileStitchHyperfabricExact as Stitch
import DASHI.Topology.TextileStitchOperationalSemanticsExact as Operational

------------------------------------------------------------------------
-- Generic crochet hook micro-semantics.
--
-- Completed crochet macro-states in TextileStitchOperationalSemanticsExact
-- intentionally expose one distinguished live working loop.  During actual
-- hook manipulation, additional loops may be temporarily held.  This module
-- represents that missing state coordinate without pretending that one generic
-- transition sequence is the exact recipe for every named crochet stitch.
------------------------------------------------------------------------

record CrochetHookMicroState : Set where
  constructor crochet-hook-micro-state
  field
    fabricState : Stitch.StitchState
    workingLoop : Stitch.LoopId
    heldHookLoops : List Stitch.LoopId

open CrochetHookMicroState public

hookLoopStack : CrochetHookMicroState → List Stitch.LoopId
hookLoopStack state = workingLoop state ∷ heldHookLoops state

completedToMicro :
  Operational.CrochetCompletedState → CrochetHookMicroState
completedToMicro completed =
  crochet-hook-micro-state
    (Operational.fabricState completed)
    (Operational.workingLoop completed)
    []

completedEmbeddingHasNoHeldLoops :
  (completed : Operational.CrochetCompletedState) →
  heldHookLoops (completedToMicro completed) ≡ []
completedEmbeddingHasNoHeldLoops completed = refl

------------------------------------------------------------------------
-- Primitive structural hook-stack transitions.
------------------------------------------------------------------------

data CrochetMicroTransition :
    CrochetHookMicroState → CrochetHookMicroState → Set where

  holdAdditionalLoop :
    ∀ {fabric working held extra} →
    CrochetMicroTransition
      (crochet-hook-micro-state fabric working held)
      (crochet-hook-micro-state fabric working (extra ∷ held))

  replaceWorkingLoop :
    ∀ {fabric old new held} →
    CrochetMicroTransition
      (crochet-hook-micro-state fabric old held)
      (crochet-hook-micro-state fabric new held)

  pullThroughOneHeldLoop :
    ∀ {fabric working held rest} →
    CrochetMicroTransition
      (crochet-hook-micro-state fabric working (held ∷ rest))
      (crochet-hook-micro-state fabric working rest)

------------------------------------------------------------------------
-- A finished microstate is one in which the temporary hook stack has reduced
-- back to the distinguished working loop.  Turning it back into the canonical
-- completed macro-state additionally requires the canonical frontier witness.
------------------------------------------------------------------------

record CrochetMicroFinished (state : CrochetHookMicroState) : Set where
  constructor crochet-micro-finished
  field
    noTemporaryHeldLoops : heldHookLoops state ≡ []
    workingLoopIsCanonicalFrontier :
      Stitch.liveLoops (Stitch.frontier (fabricState state))
      ≡ workingLoop state ∷ []

open CrochetMicroFinished public

finishedMicroToCompleted :
  (state : CrochetHookMicroState) →
  CrochetMicroFinished state →
  Operational.CrochetCompletedState
finishedMicroToCompleted state finished =
  Operational.crochet-completed-state
    (fabricState state)
    (workingLoop state)
    (workingLoopIsCanonicalFrontier finished)

completedRoundTrip :
  (completed : Operational.CrochetCompletedState) →
  finishedMicroToCompleted
    (completedToMicro completed)
    (crochet-micro-finished
      refl
      (Operational.onlyWorkingLoopIsLive completed))
  ≡ completed
completedRoundTrip
  (Operational.crochet-completed-state fabric working witness) = refl

------------------------------------------------------------------------
-- Boundary: this is the reusable hook-stack machine, not a sourced exact
-- account of single crochet, half-double crochet, double crochet, etc.
------------------------------------------------------------------------

data GenericHookStackDeterminesNamedStitchRecipe : Set where

genericHookStackDoesNotDetermineNamedStitchRecipe :
  GenericHookStackDeterminesNamedStitchRecipe → ⊥
genericHookStackDoesNotDetermineNamedStitchRecipe ()
