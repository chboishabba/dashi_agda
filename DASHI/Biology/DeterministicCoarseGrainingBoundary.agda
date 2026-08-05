module DASHI.Biology.DeterministicCoarseGrainingBoundary where

open import DASHI.Core.Prelude

import DASHI.Biology.StateDependentMultiplexTransducer as Stateful

------------------------------------------------------------------------
-- Deterministic microscopic dynamics can fail to induce a closed deterministic
-- macrodynamics after coarse-graining when the projection discards a hidden
-- state variable.  Effective uncertainty therefore need not be promoted to
-- ontological randomness.

MicroState : Set
MicroState = Bool × Bool

macroProject : MicroState → Bool
macroProject = proj₁

microStep : MicroState → MicroState
microStep (visible , hidden) =
  Stateful.xor visible hidden , hidden

microA : MicroState
microA = false , false

microB : MicroState
microB = false , true

microStatesShareMacrostate :
  macroProject microA ≡ macroProject microB
microStatesShareMacrostate = refl

microANextMacro :
  macroProject (microStep microA) ≡ false
microANextMacro = refl

microBNextMacro :
  macroProject (microStep microB) ≡ true
microBNextMacro = refl

------------------------------------------------------------------------
-- There is no Bool-level deterministic update f that commutes with this
-- projection for every microscopic state.

noClosedMacroDynamics :
  (f : Bool → Bool) →
  ((m : MicroState) → macroProject (microStep m) ≡ f (macroProject m)) →
  ⊥
noClosedMacroDynamics f commutes =
  let
    fromA : false ≡ f false
    fromA = commutes microA

    fromB : true ≡ f false
    fromB = commutes microB

    impossible : false ≡ true
    impossible = trans fromA (sym fromB)
  in
  Stateful.false≢true impossible

record DeterministicCoarseGrainingBoundary : Set where
  constructor deterministicCoarseGrainingBoundary
  field
    deterministicMicrodynamicsTracked : Bool
    deterministicMicrodynamicsTrackedIsTrue :
      deterministicMicrodynamicsTracked ≡ true

    coarseProjectionCanLoseClosure : Bool
    coarseProjectionCanLoseClosureIsTrue :
      coarseProjectionCanLoseClosure ≡ true

    stochasticEffectiveModelImpliesOnticRandomness : Bool
    stochasticEffectiveModelImpliesOnticRandomnessIsFalse :
      stochasticEffectiveModelImpliesOnticRandomness ≡ false

    quantumOntologyResolved : Bool
    quantumOntologyResolvedIsFalse :
      quantumOntologyResolved ≡ false

canonicalDeterministicCoarseGrainingBoundary :
  DeterministicCoarseGrainingBoundary
canonicalDeterministicCoarseGrainingBoundary =
  deterministicCoarseGrainingBoundary
    true refl
    true refl
    false refl
    false refl
