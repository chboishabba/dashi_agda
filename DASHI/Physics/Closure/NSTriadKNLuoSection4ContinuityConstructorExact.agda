module DASHI.Physics.Closure.NSTriadKNLuoSection4ContinuityConstructorExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Remove two opaque Section-4 tokens.  The Step-1 conclusion is the literal
-- package of the J11 lower/upper, J12 and J2 bounds.  The final continuity
-- conclusion is exactly the terminal-continuity proposition produced by the
-- mean-value/Gronwall stage, rather than an unrelated proposition selected by
-- the caller.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNLuoPerModeCommutatorEvolutionExact as Evolution

record LuoStep1ComponentBounds
    {stateLevel scalarLevel : Level}
    {State : Set stateLevel}
    {Scalar : Set scalarLevel}
    (evolution : Evolution.LuoPerModeCommutatorEvolution State Scalar)
    (state : State)
    (lowModeBound highModeBound : Nat → Scalar)
    : Set (lsuc (stateLevel ⊔ scalarLevel)) where
  field
    J11LowerHalfBound :
      (shell : Nat) →
      Evolution.lessOrEqual evolution
        (Evolution.lowerHalfRange evolution shell state)
        (lowModeBound shell)

    J11UpperHalfBound :
      (shell : Nat) →
      Evolution.lessOrEqual evolution
        (Evolution.upperHalfRange evolution shell state)
        (highModeBound shell)

    J12Bound :
      (shell : Nat) →
      Evolution.lessOrEqual evolution
        (Evolution.J12 evolution shell state)
        (highModeBound shell)

    J2Bound :
      (shell : Nat) →
      Evolution.lessOrEqual evolution
        (Evolution.J2 evolution shell state)
        (highModeBound shell)

open LuoStep1ComponentBounds public

step1DyadicBookkeeping :
  ∀ {stateLevel scalarLevel}
    {State : Set stateLevel}
    {Scalar : Set scalarLevel}
    {evolution : Evolution.LuoPerModeCommutatorEvolution State Scalar}
    {state : State}
    {lowModeBound highModeBound : Nat → Scalar} →
  LuoStep1ComponentBounds
    evolution state lowModeBound highModeBound →
  Evolution.LuoSection4Step1DyadicRangeBookkeeping evolution state
step1DyadicBookkeeping
  {lowModeBound = low}
  {highModeBound = high}
  bounds = record
    { lowModeBound = low
    ; highModeBound = high
    ; J11LowerHalfBound = J11LowerHalfBound bounds
    ; J11UpperHalfBound = J11UpperHalfBound bounds
    ; J12Bound = J12Bound bounds
    ; J2Bound = J2Bound bounds
    ; Step1LowModesBounded =
        LuoStep1ComponentBounds _ _ low high
    ; step1LowModesBounded = bounds
    }

record LuoSection4ContinuityInputs
    {stateLevel scalarLevel timeLevel : Level}
    {State : Set stateLevel}
    {Scalar : Set scalarLevel}
    (evolution : Evolution.LuoPerModeCommutatorEvolution State Scalar)
    (Time : Set timeLevel)
    : Set (lsuc (stateLevel ⊔ scalarLevel ⊔ timeLevel)) where
  field
    state : State
    alpha : Scalar

    AlphaAboveOne : Set scalarLevel
    alphaAboveOne : AlphaAboveOne

    modeDecay : Nat → Scalar
    modeDecayMeaning : Set scalarLevel
    modeDecayMeaningWitness : modeDecayMeaning

    lowModeBound highModeBound : Nat → Scalar
    step1Bounds :
      LuoStep1ComponentBounds
        evolution state lowModeBound highModeBound

    step2ContinuityGronwall :
      Evolution.LuoSection4Step2ContinuityGronwall
        evolution state Time

    DecayMakesDyadicBoundsSummable : Set scalarLevel
    decayMakesDyadicBoundsSummable :
      DecayMakesDyadicBoundsSummable

open LuoSection4ContinuityInputs public

section4ContinuityBootstrap :
  ∀ {stateLevel scalarLevel timeLevel}
    {State : Set stateLevel}
    {Scalar : Set scalarLevel}
    {evolution : Evolution.LuoPerModeCommutatorEvolution State Scalar}
    {Time : Set timeLevel} →
  LuoSection4ContinuityInputs evolution Time →
  Evolution.LuoSection4ContinuityBootstrap evolution
section4ContinuityBootstrap {Time = Time} inputs = record
  { state = state inputs
  ; alpha = alpha inputs
  ; AlphaAboveOne = AlphaAboveOne inputs
  ; alphaAboveOne = alphaAboveOne inputs
  ; modeDecay = modeDecay inputs
  ; modeDecayMeaning = modeDecayMeaning inputs
  ; modeDecayMeaningWitness = modeDecayMeaningWitness inputs
  ; step1DyadicBookkeeping =
      step1DyadicBookkeeping (step1Bounds inputs)
  ; Time = Time
  ; step2ContinuityGronwall = step2ContinuityGronwall inputs
  ; DecayMakesDyadicBoundsSummable =
      DecayMakesDyadicBoundsSummable inputs
  ; decayMakesDyadicBoundsSummable =
      decayMakesDyadicBoundsSummable inputs
  ; GronwallContinuityConclusion =
      Evolution.ContinuityAtTerminal
        (step2ContinuityGronwall inputs)
  ; sourceStep1AndStep2GiveContinuity =
      λ alphaProof decayMeaning step1Proof summability continuity → continuity
  }

section4OpaqueConclusionRemoved : Bool
section4OpaqueConclusionRemoved = true

section4OpaqueConclusionRemovedIsTrue :
  section4OpaqueConclusionRemoved ≡ true
section4OpaqueConclusionRemovedIsTrue = refl
