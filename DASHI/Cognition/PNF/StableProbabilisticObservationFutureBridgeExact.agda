module DASHI.Cognition.PNF.StableProbabilisticObservationFutureBridgeExact where

------------------------------------------------------------------------
-- PROBABILISTIC-OBSERVATION FUTURE QUOTIENT
--
-- State evolution is deterministic under supplied actions, but each state has
-- a normalized rational binary observation law.  Stable partition refinement
-- on those probability-valued observations is enough to prove equality of the
-- complete trace-indexed probability future kernel.
--
-- This is a genuine probabilistic future-equivalence bridge, while remaining
-- distinct from full stochastic-transition bisimulation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.GenericFuturePartitionRefinementExact as Refine
import DASHI.Cognition.PNF.RationalProbabilityFutureKernelExact as Prob

probabilityKernelFromDynamics :
  ∀ {State Action : Set} →
  (observe : State → Prob.BinaryProbability) →
  (step : Action → State → State) →
  Prob.RationalProbabilityFutureKernel State Action
probabilityKernelFromDynamics observe step =
  Prob.rationalProbabilityFutureKernel λ state actions →
    observe (Refine.run step actions state)

stableProbabilisticPairIsFutureEquivalent :
  ∀ {State Action : Set}
    {observe : State → Prob.BinaryProbability}
    {step : Action → State → State}
    {depth : Nat}
    (stable : Refine.StableAt depth observe step)
    {left right : State} →
  Refine.RefinesToDepth depth observe step left right →
  Prob.ProbabilityFutureEquivalent
    (probabilityKernelFromDynamics observe step) left right
stableProbabilisticPairIsFutureEquivalent
  {observe = observe} {step = step} {depth = depth}
  stable related =
  Prob.probabilityFutureEquivalent proof
  where
    proof : (actions : List _) →
      Prob.distribution (probabilityKernelFromDynamics observe step) _ actions
      ≡ Prob.distribution (probabilityKernelFromDynamics observe step) _ actions
    proof actions =
      Refine.traceObservationFromDepth actions
        (Refine.stablePairLifts stable related (length actions))

------------------------------------------------------------------------
-- A stable probabilistic partition therefore yields a future-safe projection
-- whenever equality of coarse codes implies the stable relation.
------------------------------------------------------------------------

record StableProbabilityPartition
    {State Action Coarse : Set}
    (observe : State → Prob.BinaryProbability)
    (step : Action → State → State)
    (coarsen : State → Coarse) : Set₁ where
  field
    depth : Nat
    stable : Refine.StableAt depth observe step
    coarseKernelContained :
      ∀ {left right} →
      coarsen left ≡ coarsen right →
      Refine.RefinesToDepth depth observe step left right

open StableProbabilityPartition public

stableProbabilityPartitionIsFutureSafe :
  ∀ {State Action Coarse}
    {observe : State → Prob.BinaryProbability}
    {step : Action → State → State}
    {coarsen : State → Coarse} →
  StableProbabilityPartition observe step coarsen →
  ∀ {left right} →
  coarsen left ≡ coarsen right →
  Prob.ProbabilityFutureEquivalent
    (probabilityKernelFromDynamics observe step) left right
stableProbabilityPartitionIsFutureSafe partition coarseEqual =
  stableProbabilisticPairIsFutureEquivalent
    (stable partition)
    (coarseKernelContained partition coarseEqual)

------------------------------------------------------------------------
-- Boundary: stochastic state transitions require equality of probability mass
-- transferred into equivalence classes (probabilistic bisimulation).  This
-- module closes the stochastic-observation case rather than conflating it with
-- that stronger problem.
------------------------------------------------------------------------
