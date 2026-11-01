{-# OPTIONS --safe #-}
module DASHI.Physics.Dynamics.SingularBasinFiniteWitnessExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Closure.Basin as Basin
import DASHI.Physics.Dynamics.SingularBasinReductionExact as SBR

------------------------------------------------------------------------
-- Constructive finite obstruction fixture.
--
-- This is NOT asserted to be the Yanchuk et al. differential equation.
-- It is an exact finite witness for the theorem shape exposed by that work:
--
--   * one narrow/full-state route belongs to the full basin;
--   * its reduced image is excluded by the reduced basin;
--   * another full state has the same reduced image but lies outside the full
--     basin.
--
-- Consequently reduction loses both basin preservation and enough information
-- to reconstruct full basin membership from the reduced coordinate alone.
------------------------------------------------------------------------

data FullState : Set where
  targetState : FullState
  funnelState : FullState
  outsideState : FullState

data ReducedState : Set where
  reducedTarget : ReducedState
  reducedOther : ReducedState

fullStep : FullState → FullState
fullStep targetState = targetState
fullStep funnelState = targetState
fullStep outsideState = outsideState

data FullStableShell : FullState → Set where
  targetStable : FullStableShell targetState

data FullInBasin : FullState → Set where
  targetInBasin : FullInBasin targetState
  funnelInBasin : FullInBasin funnelState

fullEventually :
  ∀ x →
  FullInBasin x →
  Basin.Eventually fullStep FullStableShell x
fullEventually targetState targetInBasin =
  Basin.now targetStable
fullEventually funnelState funnelInBasin =
  Basin.later (Basin.now targetStable)

fullBasinStep :
  ∀ x →
  FullInBasin x →
  FullInBasin (fullStep x)
fullBasinStep targetState targetInBasin =
  targetInBasin
fullBasinStep funnelState funnelInBasin =
  targetInBasin

finiteFullBasin : Basin.Basin FullState
finiteFullBasin =
  record
    { step = fullStep
    ; StableShell = FullStableShell
    ; InBasin = FullInBasin
    ; basin-eventually-stable = fullEventually
    ; basin-step = fullBasinStep
    }

reducedStep : ReducedState → ReducedState
reducedStep reducedTarget = reducedTarget
reducedStep reducedOther = reducedOther

data ReducedStableShell : ReducedState → Set where
  reducedTargetStable : ReducedStableShell reducedTarget

data ReducedInBasin : ReducedState → Set where
  reducedTargetInBasin : ReducedInBasin reducedTarget

reducedEventually :
  ∀ x →
  ReducedInBasin x →
  Basin.Eventually reducedStep ReducedStableShell x
reducedEventually reducedTarget reducedTargetInBasin =
  Basin.now reducedTargetStable

reducedBasinStep :
  ∀ x →
  ReducedInBasin x →
  ReducedInBasin (reducedStep x)
reducedBasinStep reducedTarget reducedTargetInBasin =
  reducedTargetInBasin

finiteReducedBasin : Basin.Basin ReducedState
finiteReducedBasin =
  record
    { step = reducedStep
    ; StableShell = ReducedStableShell
    ; InBasin = ReducedInBasin
    ; basin-eventually-stable = reducedEventually
    ; basin-step = reducedBasinStep
    }

project : FullState → ReducedState
project targetState = reducedTarget
project funnelState = reducedOther
project outsideState = reducedOther

finiteReduction : SBR.BasinReduction FullState ReducedState
finiteReduction =
  record
    { project = project
    ; fullBasin = finiteFullBasin
    ; reducedBasin = finiteReducedBasin
    }

reduced-other-not-in-basin :
  ¬ ReducedInBasin reducedOther
reduced-other-not-in-basin ()

outside-not-in-full-basin :
  ¬ FullInBasin outsideState
outside-not-in-full-basin ()

finite-basin-reduction-failure :
  SBR.BasinReductionFailure finiteReduction
finite-basin-reduction-failure =
  record
    { witness = funnelState
    ; fullMember = funnelInBasin
    ; reducedExcluded = reduced-other-not-in-basin
    }

finite-reduction-not-basin-preserving :
  ¬ SBR.BasinPreserving finiteReduction
finite-reduction-not-basin-preserving =
  SBR.failure-refutes-preservation
    finite-basin-reduction-failure

finite-basin-projection-collision :
  SBR.BasinProjectionCollision finiteReduction
finite-basin-projection-collision =
  record
    { inside = funnelState
    ; outside = outsideState
    ; sameReducedState = refl
    ; insideFullBasin = funnelInBasin
    ; outsideFullBasin = outside-not-in-full-basin
    }

finite-full-basin-does-not-factor-through-reduction :
  ¬ SBR.PredicateFactorisation
      project
      FullInBasin
finite-full-basin-does-not-factor-through-reduction =
  SBR.basin-collision-refutes-full-membership-factorisation
    finite-basin-projection-collision
