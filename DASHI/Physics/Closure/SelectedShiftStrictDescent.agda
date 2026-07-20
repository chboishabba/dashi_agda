{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.SelectedShiftStrictDescent where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; _<_ ; z≤n)
open import Data.Nat.Properties as NatP
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import DASHI.Core.BasinFiniteDescent
open import DASHI.Physics.Closure.ShiftFiniteTangentSemigroup as Shift
open import DASHI.Physics.Closure.ShiftFiniteNormedTangent as Normed

------------------------------------------------------------------------
-- Strict descent for the actual selected finite shift-pressure kernel.
--
-- This is not a generic countdown surrogate.  The step is exactly
-- Shift.finiteDerivativeStep, which is definitionally coherent with the
-- repository's implemented shiftPressureAdvance dynamics.

SelectedState : Set
SelectedState = Shift.ShiftFinitePerturbation

selectedStep : SelectedState → SelectedState
selectedStep = Shift.finiteDerivativeStep

selectedCost : SelectedState → Nat
selectedCost = Normed.finiteNorm

SelectedBasin : SelectedState → Set
SelectedBasin _ = Nat

SelectedFixed : SelectedState → Set
SelectedFixed p = p ≡ Shift.zeroPerturbation

selected-fixed-sound : ∀ {p} → SelectedFixed p → selectedStep p ≡ p
selected-fixed-sound {Shift.zeroPerturbation} refl = refl

selected-preserves-basin : ∀ {p} → SelectedBasin p → SelectedBasin (selectedStep p)
selected-preserves-basin _ = zero

selected-strict-or-fixed :
  ∀ {p} → SelectedBasin p →
  selectedCost (selectedStep p) < selectedCost p ⊎ SelectedFixed p
selected-strict-or-fixed {Shift.startPerturbation} _ =
  inj₁ (NatP.n<1+n (suc zero))
selected-strict-or-fixed {Shift.nextPerturbation} _ =
  inj₁ (NatP.n<1+n zero)
selected-strict-or-fixed {Shift.zeroPerturbation} _ =
  inj₂ refl

selectedShiftStrictDescent : BasinStrictDescent SelectedState
selectedShiftStrictDescent =
  record
    { step = selectedStep
    ; Basin = SelectedBasin
    ; Fixed = SelectedFixed
    ; cost = selectedCost
    ; fixed-sound = selected-fixed-sound
    ; preserves-basin = selected-preserves-basin
    ; strict-or-fixed = selected-strict-or-fixed
    }

selected-start-witness :
  FiniteDescentWitness selectedShiftStrictDescent Shift.startPerturbation
selected-start-witness =
  record
    { endpoint = Shift.zeroPerturbation
    ; steps = suc (suc zero)
    ; endpoint-in-basin = zero
    ; endpoint-fixed = refl
    ; endpoint-fixed-sound = refl
    ; endpoint-cost-bounded = z≤n
    }

selected-next-witness :
  FiniteDescentWitness selectedShiftStrictDescent Shift.nextPerturbation
selected-next-witness =
  record
    { endpoint = Shift.zeroPerturbation
    ; steps = suc zero
    ; endpoint-in-basin = zero
    ; endpoint-fixed = refl
    ; endpoint-fixed-sound = refl
    ; endpoint-cost-bounded = z≤n
    }

selected-two-step-closure :
  selectedStep (selectedStep Shift.startPerturbation) ≡ Shift.zeroPerturbation
selected-two-step-closure = refl
