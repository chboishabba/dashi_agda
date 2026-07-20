{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.SelectedShiftScaleDefects where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_≤_; z≤n)

open import DASHI.Core.MultiscaleMDL
open import DASHI.Core.ApproximateMultiscaleNaturality
open import DASHI.Physics.Closure.ShiftFiniteTangentSemigroup as Shift

------------------------------------------------------------------------
-- The selected shift dynamics is scale-independent on the finite perturbation
-- carrier.  Projection and lift are identities, so the actual selected kernel
-- commutes exactly at every scale.  Consequently its commutation defects are
-- identically zero and every finite partial sum is zero.

selectedShiftTower : MultiscaleCarrier
selectedShiftTower =
  record
    { Carrier = λ _ → Shift.ShiftFinitePerturbation
    ; project = λ x → x
    ; lift = λ x → x
    ; project-lift = λ _ → refl
    }

selectedShiftKernelTower : KernelTower selectedShiftTower
selectedShiftKernelTower =
  record
    { kernel = λ _ → Shift.finiteDerivativeStep
    ; project-kernel = λ _ → refl
    }

-- This metric is used only to measure the naturality defect.  Exact equality of
-- the two commuting paths already carries the substantive result; no claim that
-- this zero pseudometric separates physical states is made.
selectedDefectMetric : TowerMetric selectedShiftTower
selectedDefectMetric =
  record
    { distance = λ _ _ _ → zero
    ; self-zero = λ _ _ → refl
    ; triangle = λ _ _ _ _ → z≤n
    }

selectedApproximateTower :
  ApproximateKernelTower selectedShiftTower selectedDefectMetric
selectedApproximateTower =
  exact-as-approximate selectedDefectMetric selectedShiftKernelTower

selected-defect-zero :
  ∀ {j} (x : Carrier selectedShiftTower (suc j)) →
  commutationError selectedApproximateTower x ≡ zero
selected-defect-zero x = refl

selectedGlobalBound : Nat → Nat
selectedGlobalBound _ = zero

selectedPartialDefect : Nat → Nat
selectedPartialDefect zero = zero
selectedPartialDefect (suc n) =
  selectedGlobalBound n + selectedPartialDefect n

selected-partial-defect-zero : ∀ n → selectedPartialDefect n ≡ zero
selected-partial-defect-zero zero = refl
selected-partial-defect-zero (suc n)
  rewrite selected-partial-defect-zero n = refl

record ExactVanishingDefects : Set where
  constructor exact-vanishing-defects
  field
    bound : Nat → Nat
    bound-zero : ∀ j → bound j ≡ zero
open ExactVanishingDefects public

record ExactSummableDefects : Set where
  constructor exact-summable-defects
  field
    partialSum : Nat → Nat
    total : Nat
    partial-zero : ∀ n → partialSum n ≡ zero
    total-zero : total ≡ zero
    bounded : ∀ n → partialSum n ≤ total
open ExactSummableDefects public

selectedVanishingDefects : ExactVanishingDefects
selectedVanishingDefects =
  exact-vanishing-defects selectedGlobalBound (λ _ → refl)

selectedSummableDefects : ExactSummableDefects
selectedSummableDefects =
  exact-summable-defects
    selectedPartialDefect
    zero
    selected-partial-defect-zero
    refl
    bounded
  where
  bounded : ∀ n → selectedPartialDefect n ≤ zero
  bounded n rewrite selected-partial-defect-zero n = z≤n

selectedControlledErrors :
  ControlledErrorFamily selectedDefectMetric selectedApproximateTower
selectedControlledErrors =
  record
    { globalBound = selectedGlobalBound
    ; pointwiseBound = λ _ → z≤n
    ; tendsToZero = ExactVanishingDefects
    ; summable = ExactSummableDefects
    }
