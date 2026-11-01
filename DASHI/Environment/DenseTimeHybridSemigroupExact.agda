module DASHI.Environment.DenseTimeHybridSemigroupExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Give LES an actual dense-time flow law rather than treating continuous
-- evolution as one opaque discrete `flow` command.  Time is rational here:
-- enough to express an exact semigroup law and arbitrary finite rational
-- durations without claiming a completed real-analysis/ODE solver.
--
-- REFERENCE / MOTIVATION
--
-- Rajeev Alur, Costas Courcoubetis, Thomas A. Henzinger, Pei-Hsin Ho,
-- "Hybrid Automata: An Algorithmic Approach to the Specification and
-- Verification of Hybrid Systems", Hybrid Systems I, LNCS 736, 1993.
--
-- The hybrid-systems literature motivates continuous flow plus guarded jumps.
-- The rational-time semigroup and preservation theorem below are DASHI
-- constructions; they do not claim unrestricted hybrid reachability decidable.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)

record DenseTimeFlow (State : Set) : Set₁ where
  constructor denseTimeFlow
  field
    flow : ℚ → State → State
    flowZero : ∀ state → flow 0ℚ state ≡ state
    flowAdd :
      ∀ dt₁ dt₂ state →
      flow (dt₁ + dt₂) state ≡ flow dt₂ (flow dt₁ state)

open DenseTimeFlow public

record FlowInvariant
    {State : Set}
    (system : DenseTimeFlow State)
    (Safe : State → Set) : Set₁ where
  constructor flowInvariant
  field
    flowPreserves :
      ∀ dt state →
      Safe state →
      Safe (flow system dt state)

open FlowInvariant public

flowTwoDurationsPreserve :
  ∀ {State}
    {system : DenseTimeFlow State}
    {Safe : State → Set} →
  FlowInvariant system Safe →
  (dt₁ dt₂ : ℚ) →
  (state : State) →
  Safe state →
  Safe (flow system (dt₁ + dt₂) state)
flowTwoDurationsPreserve {system = system} invariant dt₁ dt₂ state safe
  rewrite flowAdd system dt₁ dt₂ state =
  flowPreserves invariant dt₂ (flow system dt₁ state)
    (flowPreserves invariant dt₁ state safe)

record DenseTimeJumpSystem (State Jump : Set) : Set₁ where
  constructor denseTimeJumpSystem
  field
    continuous : DenseTimeFlow State
    jump : Jump → State → State

open DenseTimeJumpSystem public

data DenseHybridCommand (Jump : Set) : Set where
  evolve : ℚ → DenseHybridCommand Jump
  discrete : Jump → DenseHybridCommand Jump

stepDenseHybrid :
  ∀ {State Jump} →
  DenseTimeJumpSystem State Jump →
  DenseHybridCommand Jump →
  State → State
stepDenseHybrid system (evolve dt) state =
  flow (continuous system) dt state
stepDenseHybrid system (discrete action) state =
  jump system action state

record DenseHybridInvariant
    {State Jump : Set}
    (system : DenseTimeJumpSystem State Jump)
    (Safe : State → Set) : Set₁ where
  constructor denseHybridInvariant
  field
    continuousSafe : FlowInvariant (continuous system) Safe
    jumpSafe :
      ∀ action state →
      Safe state →
      Safe (jump system action state)

open DenseHybridInvariant public

oneDenseHybridCommandPreservesSafe :
  ∀ {State Jump}
    {system : DenseTimeJumpSystem State Jump}
    {Safe : State → Set} →
  DenseHybridInvariant system Safe →
  (command : DenseHybridCommand Jump) →
  (state : State) →
  Safe state →
  Safe (stepDenseHybrid system command state)
oneDenseHybridCommandPreservesSafe invariant (evolve dt) state safe =
  flowPreserves (continuousSafe invariant) dt state safe
oneDenseHybridCommandPreservesSafe invariant (discrete action) state safe =
  jumpSafe invariant action state safe

record DenseTimeHybridBoundary : Set where
  constructor denseTimeHybridBoundary
  field
    flowHasExplicitDenseTimeParameter : Bool
    sequentialDurationsObeySemigroupLaw : Bool
    invariantsMustSurviveEveryDeclaredDuration : Bool
    jumpsRemainSeparateFromContinuousFlow : Bool
    rationalDenseTimeDoesNotClaimARealODESolution : Bool

canonicalDenseTimeHybridBoundary : DenseTimeHybridBoundary
canonicalDenseTimeHybridBoundary =
  denseTimeHybridBoundary true true true true true
