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
-- that decay into continuity and continuation.  These are deliberately two
-- different obligations on one solution carrier.
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
    add multiply : Scalar → Scalar → Scalar
    lessOrEqual : Scalar → Scalar → Set scalarLevel

    -- Source-shaped version of Luo equation (4.2).  The concrete carrier owns
    -- the dyadic powers and finite near-shell/tail sums; this interface keeps
    -- their exact repository representation explicit rather than hiding them
    -- behind a generic 'standard estimate' marker.
    perModeEvolutionInequality :
      (shell : Nat) → (u : State) →
      lessOrEqual
        (add
          (timeDerivativeShellL2Squared shell u)
          (shellDissipation shell u))
        (add
          (lowToNearInteraction shell u)
          (highTailInteraction shell u))

    lowToNearHasLuoDyadicMeaning : Set scalarLevel
    lowToNearHasLuoDyadicMeaningWitness :
      lowToNearHasLuoDyadicMeaning

    highTailHasLuoDyadicMeaning : Set scalarLevel
    highTailHasLuoDyadicMeaningWitness :
      highTailHasLuoDyadicMeaning

open LuoPerModeCommutatorEvolution public

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

    GronwallContinuityConclusion : Set scalarLevel

    equation42ImpliesContinuity :
      ((shell : Nat) →
        lessOrEqual evolution
          (add evolution
            (timeDerivativeShellL2Squared evolution shell state)
            (shellDissipation evolution shell state))
          (add evolution
            (lowToNearInteraction evolution shell state)
            (highTailInteraction evolution shell state))) →
      AlphaAboveOne →
      modeDecayMeaning →
      GronwallContinuityConclusion

open LuoSection4ContinuityBootstrap public

luoPerModeEquation42TargetConstructed : Bool
luoPerModeEquation42TargetConstructed = true

luoSection4ContinuityBootstrapTargetConstructed : Bool
luoSection4ContinuityBootstrapTargetConstructed = true

luoPerModeEquation42PhysicallyInhabited : Bool
luoPerModeEquation42PhysicallyInhabited = false

luoPerModeEquation42TargetConstructedIsTrue :
  luoPerModeEquation42TargetConstructed ≡ true
luoPerModeEquation42TargetConstructedIsTrue = refl

luoSection4ContinuityBootstrapTargetConstructedIsTrue :
  luoSection4ContinuityBootstrapTargetConstructed ≡ true
luoSection4ContinuityBootstrapTargetConstructedIsTrue = refl

luoPerModeEquation42PhysicallyInhabitedIsFalse :
  luoPerModeEquation42PhysicallyInhabited ≡ false
luoPerModeEquation42PhysicallyInhabitedIsFalse = refl
