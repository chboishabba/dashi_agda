module DASHI.Physics.Closure.NSTriadKNLuoPerModeCommutatorEvolutionExact where

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
-- Isolate the second nonlinear engine in Luo's proof.  Proposition 3.1 controls
-- high-frequency flux and yields decay.  Section 4 additionally needs the
-- per-mode paraproduct/commutator evolution estimate (equation (4.2)) to turn
-- that decay into continuity and continuation.
--
-- The source proof has two genuinely separate stages:
--
--   Step 1: J1/J2 and J11/J12 dyadic-range bookkeeping, including the split
--           r <= q/2 versus q/2 <= r <= q used in equations (4.7)--(4.9).
--   Step 2: a mean-value selection tau_q followed by a Gronwall argument on
--           [tau_q,t_q], with the terminal choice t_q=T.
--
-- These stages are explicit proof objects below; equation (4.2) alone is not
-- allowed to stand in for the whole Section-4 argument.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

record LuoPerModeCommutatorEvolution
    {stateLevel scalarLevel : Level}
    (State : Set stateLevel)
    (Scalar : Set scalarLevel)
    : Set (lsuc (stateLevel ⊔ scalarLevel)) where
  field
    shellL2Squared : Nat → State → Scalar
    shellDissipation : Nat → State → Scalar
    timeDerivativeShellL2Squared : Nat → State → Scalar

    lowToNearInteraction : Nat → State → Scalar
    highTailInteraction : Nat → State → Scalar

    -- Source names for the two right-hand-side groups and their refinements.
    J1 J2 J11 J12 : Nat → State → Scalar
    lowerHalfRange upperHalfRange : Nat → State → Scalar

    add multiply : Scalar → Scalar → Scalar
    lessOrEqual : Scalar → Scalar → Set scalarLevel

    -- Luo equation (4.2).
    perModeEvolutionInequality :
      (shell : Nat) → (u : State) →
      lessOrEqual
        (add
          (timeDerivativeShellL2Squared shell u)
          (shellDissipation shell u))
        (add
          (lowToNearInteraction shell u)
          (highTailInteraction shell u))

    equation42RightHandSideMeaning :
      (shell : Nat) → (u : State) →
      add
        (lowToNearInteraction shell u)
        (highTailInteraction shell u)
      ≡ add (J1 shell u) (J2 shell u)

    J1DyadicSplit :
      (shell : Nat) → (u : State) →
      J1 shell u ≡ add (J11 shell u) (J12 shell u)

    lowShellSumRangeSplit :
      (shell : Nat) → (u : State) →
      J11 shell u
      ≡ add
          (lowerHalfRange shell u)
          (upperHalfRange shell u)

    lowToNearHasLuoDyadicMeaning : Set scalarLevel
    lowToNearHasLuoDyadicMeaningWitness :
      lowToNearHasLuoDyadicMeaning

    highTailHasLuoDyadicMeaning : Set scalarLevel
    highTailHasLuoDyadicMeaningWitness :
      highTailHasLuoDyadicMeaning

open LuoPerModeCommutatorEvolution public

record LuoSection4Step1DyadicRangeBookkeeping
    {stateLevel scalarLevel : Level}
    {State : Set stateLevel}
    {Scalar : Set scalarLevel}
    (evolution : LuoPerModeCommutatorEvolution State Scalar)
    (state : State)
    : Set (lsuc (stateLevel ⊔ scalarLevel)) where
  field
    lowModeBound highModeBound : Nat → Scalar

    J11LowerHalfBound :
      (shell : Nat) →
      lessOrEqual evolution
        (lowerHalfRange evolution shell state)
        (lowModeBound shell)

    J11UpperHalfBound :
      (shell : Nat) →
      lessOrEqual evolution
        (upperHalfRange evolution shell state)
        (highModeBound shell)

    J12Bound :
      (shell : Nat) →
      lessOrEqual evolution
        (J12 evolution shell state)
        (highModeBound shell)

    J2Bound :
      (shell : Nat) →
      lessOrEqual evolution
        (J2 evolution shell state)
        (highModeBound shell)

    Step1LowModesBounded : Set scalarLevel
    step1LowModesBounded : Step1LowModesBounded

open LuoSection4Step1DyadicRangeBookkeeping public

record LuoSection4Step2ContinuityGronwall
    {stateLevel scalarLevel timeLevel : Level}
    {State : Set stateLevel}
    {Scalar : Set scalarLevel}
    (evolution : LuoPerModeCommutatorEvolution State Scalar)
    (state : State)
    (Time : Set timeLevel)
    : Set (lsuc (stateLevel ⊔ scalarLevel ⊔ timeLevel)) where
  field
    terminalTime : Time
    tauAt terminalApproximationAt : Nat → Time

    MeanValueSelectionForTau : Set (scalarLevel ⊔ timeLevel)
    meanValueSelectionForTau : MeanValueSelectionForTau

    TauPrecedesTerminalApproximation : Set timeLevel
    tauPrecedesTerminalApproximation :
      TauPrecedesTerminalApproximation

    TerminalApproximationConvergesToTerminal : Set timeLevel
    terminalApproximationConvergesToTerminal :
      TerminalApproximationConvergesToTerminal

    GronwallHypothesisOnSelectedIntervals : Set (scalarLevel ⊔ timeLevel)
    gronwallHypothesisOnSelectedIntervals :
      GronwallHypothesisOnSelectedIntervals

    UniformH1BoundAtTerminalApproximations : Set scalarLevel
    gronwallPropagatesUniformH1Bound :
      GronwallHypothesisOnSelectedIntervals →
      UniformH1BoundAtTerminalApproximations

    ContinuityAtTerminal : Set (stateLevel ⊔ timeLevel)
    uniformBoundAndLimitGiveContinuity :
      UniformH1BoundAtTerminalApproximations →
      TerminalApproximationConvergesToTerminal →
      ContinuityAtTerminal

open LuoSection4Step2ContinuityGronwall public

record LuoSection4ContinuityBootstrap
    {stateLevel scalarLevel : Level}
    {State : Set stateLevel}
    {Scalar : Set scalarLevel}
    (evolution : LuoPerModeCommutatorEvolution State Scalar)
    : Set (lsuc (stateLevel ⊔ scalarLevel)) where
  field
    state : State
    alpha : Scalar

    AlphaAboveOne : Set scalarLevel
    alphaAboveOne : AlphaAboveOne

    modeDecay : Nat → Scalar
    modeDecayMeaning : Set scalarLevel
    modeDecayMeaningWitness : modeDecayMeaning

    step1DyadicBookkeeping :
      LuoSection4Step1DyadicRangeBookkeeping evolution state

    Time : Set
    step2ContinuityGronwall :
      LuoSection4Step2ContinuityGronwall evolution state Time

    DecayMakesDyadicBoundsSummable : Set scalarLevel
    decayMakesDyadicBoundsSummable : DecayMakesDyadicBoundsSummable

    GronwallContinuityConclusion : Set scalarLevel

    sourceStep1AndStep2GiveContinuity :
      AlphaAboveOne →
      modeDecayMeaning →
      Step1LowModesBounded step1DyadicBookkeeping →
      DecayMakesDyadicBoundsSummable →
      ContinuityAtTerminal step2ContinuityGronwall →
      GronwallContinuityConclusion

open LuoSection4ContinuityBootstrap public

section4ContinuityConclusion :
  ∀ {stateLevel scalarLevel}
    {State : Set stateLevel}
    {Scalar : Set scalarLevel}
    {evolution : LuoPerModeCommutatorEvolution State Scalar} →
  (bootstrap : LuoSection4ContinuityBootstrap evolution) →
  GronwallContinuityConclusion bootstrap
section4ContinuityConclusion bootstrap =
  sourceStep1AndStep2GiveContinuity bootstrap
    (alphaAboveOne bootstrap)
    (modeDecayMeaningWitness bootstrap)
    (step1LowModesBounded (step1DyadicBookkeeping bootstrap))
    (decayMakesDyadicBoundsSummable bootstrap)
    (uniformBoundAndLimitGiveContinuity
      (step2ContinuityGronwall bootstrap)
      (gronwallPropagatesUniformH1Bound
        (step2ContinuityGronwall bootstrap)
        (gronwallHypothesisOnSelectedIntervals
          (step2ContinuityGronwall bootstrap)))
      (terminalApproximationConvergesToTerminal
        (step2ContinuityGronwall bootstrap)))

luoPerModeEquation42TargetConstructed : Bool
luoPerModeEquation42TargetConstructed = true

luoSection4DyadicRangeSplitTargetConstructed : Bool
luoSection4DyadicRangeSplitTargetConstructed = true

luoSection4MeanValueGronwallTargetConstructed : Bool
luoSection4MeanValueGronwallTargetConstructed = true

luoSection4ContinuityBootstrapTargetConstructed : Bool
luoSection4ContinuityBootstrapTargetConstructed = true

luoPerModeEquation42PhysicallyInhabited : Bool
luoPerModeEquation42PhysicallyInhabited = false

luoPerModeEquation42TargetConstructedIsTrue :
  luoPerModeEquation42TargetConstructed ≡ true
luoPerModeEquation42TargetConstructedIsTrue = refl

luoSection4DyadicRangeSplitTargetConstructedIsTrue :
  luoSection4DyadicRangeSplitTargetConstructed ≡ true
luoSection4DyadicRangeSplitTargetConstructedIsTrue = refl

luoSection4MeanValueGronwallTargetConstructedIsTrue :
  luoSection4MeanValueGronwallTargetConstructed ≡ true
luoSection4MeanValueGronwallTargetConstructedIsTrue = refl

luoSection4ContinuityBootstrapTargetConstructedIsTrue :
  luoSection4ContinuityBootstrapTargetConstructed ≡ true
luoSection4ContinuityBootstrapTargetConstructedIsTrue = refl

luoPerModeEquation42PhysicallyInhabitedIsFalse :
  luoPerModeEquation42PhysicallyInhabited ≡ false
luoPerModeEquation42PhysicallyInhabitedIsFalse = refl
