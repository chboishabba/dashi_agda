module DASHI.Physics.Closure.NSTriadKNCubicQuadraticUniformGapNoGo where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_; _+_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality
  using (cong; subst; module ≡-Reasoning)

------------------------------------------------------------------------
-- Amplitude-homogeneity obstruction.
--
-- A genuinely cubic nonnegative form cannot be bounded by one fixed multiple
-- of a quadratic form at every amplitude. Therefore an arbitrary-data Stage-3
-- theorem must use normalisation, signed cancellation, a state-dependent
-- coefficient, or a modified energy; a raw amplitude-independent quadratic
-- majorant is not a viable endpoint.
------------------------------------------------------------------------

record CubicQuadraticScaling {s : Level} (State : Set s) : Set (lsuc s) where
  field
    scale : Nat → State → State
    nonlinear energy : State → Nat

    nonlinearCubic : ∀ factor state →
      nonlinear (scale factor state)
      ≡
      (factor * factor) * (factor * nonlinear state)

    energyQuadratic : ∀ factor state →
      energy (scale factor state)
      ≡
      (factor * factor) * energy state

open CubicQuadraticScaling public

rightFactorReassociate :
  ∀ constant square energyValue →
  constant * (square * energyValue)
  ≡ square * (constant * energyValue)
rightFactorReassociate constant square energyValue =
  begin
    constant * (square * energyValue)
  ≡⟨ Nat.*-assoc constant square energyValue ⟨
    (constant * square) * energyValue
  ≡⟨ cong (_* energyValue) (Nat.*-comm constant square) ⟩
    (square * constant) * energyValue
  ≡⟨ Nat.*-assoc square constant energyValue ⟩
    square * (constant * energyValue)
  ∎
  where open ≡-Reasoning

uniformQuadraticBoundAtScaleImpliesLinearBound :
  ∀ {s} {State : Set s}
    (S : CubicQuadraticScaling State)
    (constant : Nat)
    (uniformBound : ∀ state → nonlinear S state ≤ constant * energy S state)
    (state : State)
    (predecessor : Nat) →
  suc predecessor * nonlinear S state
  ≤ constant * energy S state
uniformQuadraticBoundAtScaleImpliesLinearBound S constant uniformBound state predecessor =
  Nat.*-cancelˡ-≤ square factoredBound
  where
  factor : Nat
  factor = suc predecessor

  square : Nat
  square = factor * factor

  uniformScaled :
    nonlinear S (scale S factor state)
    ≤ constant * energy S (scale S factor state)
  uniformScaled = uniformBound (scale S factor state)

  scaledBound :
    square * (factor * nonlinear S state)
    ≤ constant * (square * energy S state)
  scaledBound =
    subst
      (λ left → left ≤ constant * (square * energy S state))
      (nonlinearCubic S factor state)
      (subst
        (λ right → nonlinear S (scale S factor state) ≤ constant * right)
        (energyQuadratic S factor state)
        uniformScaled)

  factoredBound :
    square * (factor * nonlinear S state)
    ≤ square * (constant * energy S state)
  factoredBound =
    subst
      (λ right → square * (factor * nonlinear S state) ≤ right)
      (rightFactorReassociate constant square (energy S state))
      scaledBound

positiveCubicWitnessRefutesUniformQuadraticBound :
  ∀ {s} {State : Set s}
    (S : CubicQuadraticScaling State)
    (constant : Nat)
    (uniformBound : ∀ state → nonlinear S state ≤ constant * energy S state)
    (state : State) →
  0 < nonlinear S state →
  ⊥
positiveCubicWitnessRefutesUniformQuadraticBound S constant uniformBound state nonlinearPositive =
  Nat.<⇒≱ strictGrowth cancelledBound
  where
  base : Nat
  base = constant * energy S state

  factor : Nat
  factor = suc base

  factor≤factorTimesNonlinear :
    factor ≤ factor * nonlinear S state
  factor≤factorTimesNonlinear =
    subst
      (λ left → left ≤ factor * nonlinear S state)
      (Nat.*-identityʳ factor)
      (Nat.*-monoʳ-≤ factor nonlinearPositive)

  strictGrowth :
    constant * energy S state
    < factor * nonlinear S state
  strictGrowth =
    Nat.<-≤-trans
      (Nat.n<1+n base)
      factor≤factorTimesNonlinear

  cancelledBound :
    factor * nonlinear S state
    ≤ constant * energy S state
  cancelledBound =
    uniformQuadraticBoundAtScaleImpliesLinearBound
      S constant uniformBound state base

cubicQuadraticUniformNoGoClosed : Bool
cubicQuadraticUniformNoGoClosed = true

cubicQuadraticUniformNoGoClosedIsTrue :
  cubicQuadraticUniformNoGoClosed ≡ true
cubicQuadraticUniformNoGoClosedIsTrue = refl
