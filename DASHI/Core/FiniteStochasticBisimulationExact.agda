module DASHI.Core.FiniteStochasticBisimulationExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Exact finite stochastic analogue of current-observation quotient safety.
-- Transition rows are represented by denominator-free natural masses.  Two
-- fine states may share the same current projection only when every declared
-- action induces the same mass on every declared coarse outcome block.
--
-- REFERENCES / MOTIVATION
--
-- Norman Ferns, Prakash Panangaden, Doina Precup,
-- "Metrics for Finite Markov Decision Processes", UAI 2004, pp. 162-169.
--
-- Norman Ferns, Prakash Panangaden, Doina Precup,
-- "Bisimulation Metrics for Continuous Markov Decision Processes",
-- SIAM Journal on Computing 40(6), 2011, 1662-1714.
-- DOI: 10.1137/10080484X.
--
-- The literature supplies probabilistic bisimulation metrics.  This module is
-- a deliberately finite exact kernel-level contract and counterexample layer;
-- it does not claim the full metric/value-function theory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; z≤n; s≤s)

record ProjectedFiniteKernel
    (State Action Coarse : Set) : Set₁ where
  constructor projectedFiniteKernel
  field
    project : State → Coarse
    transitionMass : Action → State → Coarse → Nat
    rowMass : Action → State → Nat
    projectedMassBounded :
      ∀ action state coarse → transitionMass action state coarse ≤ rowMass action state

open ProjectedFiniteKernel public

record KernelBisimulation
    {State Action Coarse : Set}
    (kernel : ProjectedFiniteKernel State Action Coarse) : Set₁ where
  constructor kernelBisimulation
  field
    sameProjectionSameProjectedKernel :
      ∀ {left right} →
      project kernel left ≡ project kernel right →
      (action : Action) →
      (coarseOutcome : Coarse) →
      transitionMass kernel action left coarseOutcome
      ≡ transitionMass kernel action right coarseOutcome

open KernelBisimulation public

record KernelBisimulationDefect
    {State Action Coarse : Set}
    (kernel : ProjectedFiniteKernel State Action Coarse) : Set where
  constructor kernelBisimulationDefect
  field
    left right : State
    sameCurrentProjection : project kernel left ≡ project kernel right
    distinguishingAction : Action
    distinguishingOutcome : Coarse
    projectedTransitionMassDiffers :
      transitionMass kernel distinguishingAction left distinguishingOutcome
      ≡ transitionMass kernel distinguishingAction right distinguishingOutcome → ⊥

open KernelBisimulationDefect public

kernelDefectContradictsBisimulation :
  ∀ {State Action Coarse}
    {kernel : ProjectedFiniteKernel State Action Coarse} →
  KernelBisimulation kernel →
  KernelBisimulationDefect kernel →
  ⊥
kernelDefectContradictsBisimulation bisimulation defect =
  projectedTransitionMassDiffers defect
    (sameProjectionSameProjectedKernel bisimulation
      (sameCurrentProjection defect)
      (distinguishingAction defect)
      (distinguishingOutcome defect))

------------------------------------------------------------------------
-- Finite stochastic counterexample: same current coarse state, but the same
-- storm/intervention action sends all transition mass to different blocks.
------------------------------------------------------------------------

data DemoState : Set where
  hiddenFast hiddenSlow : DemoState

data DemoAction : Set where
  storm : DemoAction

data DemoCoarse : Set where
  sameNow lowLoad highLoad : DemoCoarse

projectDemo : DemoState → DemoCoarse
projectDemo hiddenFast = sameNow
projectDemo hiddenSlow = sameNow

massDemo : DemoAction → DemoState → DemoCoarse → Nat
massDemo storm hiddenFast sameNow = 0
massDemo storm hiddenFast lowLoad = 0
massDemo storm hiddenFast highLoad = 1
massDemo storm hiddenSlow sameNow = 0
massDemo storm hiddenSlow lowLoad = 1
massDemo storm hiddenSlow highLoad = 0

rowDemo : DemoAction → DemoState → Nat
rowDemo storm hiddenFast = 1
rowDemo storm hiddenSlow = 1

zeroLeOne : 0 ≤ 1
zeroLeOne = z≤n

oneLeOne : 1 ≤ 1
oneLeOne = s≤s z≤n

massDemoBounded :
  ∀ action state coarse → massDemo action state coarse ≤ rowDemo action state
massDemoBounded storm hiddenFast sameNow = zeroLeOne
massDemoBounded storm hiddenFast lowLoad = zeroLeOne
massDemoBounded storm hiddenFast highLoad = oneLeOne
massDemoBounded storm hiddenSlow sameNow = zeroLeOne
massDemoBounded storm hiddenSlow lowLoad = oneLeOne
massDemoBounded storm hiddenSlow highLoad = zeroLeOne

demoKernel : ProjectedFiniteKernel DemoState DemoAction DemoCoarse
demoKernel = projectedFiniteKernel projectDemo massDemo rowDemo massDemoBounded

demoKernelDefect : KernelBisimulationDefect demoKernel
demoKernelDefect = kernelBisimulationDefect
  hiddenFast hiddenSlow refl storm highLoad impossible
  where
    impossible : 1 ≡ 0 → ⊥
    impossible ()

record FiniteStochasticBoundary : Set where
  constructor finiteStochasticBoundary
  field
    sameCurrentProjectionNeedNotMeanSameTransitionLaw : Bool
    projectedKernelEqualityIsStrongerThanCurrentObservationEquality : Bool
    naturalMassKernelDoesNotByItselfSupplyProbabilityNormalization : Bool
    oneStepKernelBisimulationDoesNotByItselfSupplyValueBounds : Bool

canonicalFiniteStochasticBoundary : FiniteStochasticBoundary
canonicalFiniteStochasticBoundary =
  finiteStochasticBoundary true true true true
