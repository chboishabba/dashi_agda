{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.SelectedKernelEvidenceRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Maybe using (just; nothing)

open import DASHI.Algebra.Trit using (neg; zer; pos)
open import DASHI.Core.ApproximateMultiscaleNaturality
open import DASHI.Physics.Closure.ShiftFiniteTangentSemigroup as Shift
open import DASHI.Physics.Closure.SelectedShiftStrictDescent
open import DASHI.Physics.Closure.SelectedShiftScaleDefects
open import DASHI.Codec.VerifiedFiniteTritCoder
open import DASHI.Physics.ConstantZeroModeContinuumTheorem

selected-kernel-start-two-step :
  selectedStep (selectedStep Shift.startPerturbation) ≡ Shift.zeroPerturbation
selected-kernel-start-two-step = refl

selected-kernel-next-one-step :
  selectedStep Shift.nextPerturbation ≡ Shift.zeroPerturbation
selected-kernel-next-one-step = refl

selected-start-cost : selectedCost Shift.startPerturbation ≡ suc (suc zero)
selected-start-cost = refl

selected-next-cost : selectedCost Shift.nextPerturbation ≡ suc zero
selected-next-cost = refl

selected-fixed-cost : selectedCost Shift.zeroPerturbation ≡ zero
selected-fixed-cost = refl

selected-scale-defect-is-zero :
  commutationError selectedApproximateTower Shift.startPerturbation ≡ zero
selected-scale-defect-is-zero = refl

selected-partial-defect-at-three :
  selectedPartialDefect (suc (suc (suc zero))) ≡ zero
selected-partial-defect-at-three = selected-partial-defect-zero _

finite-coder-negative : decodeWord (encodeTrit neg) ≡ just neg
finite-coder-negative = refl

finite-coder-zero : decodeWord (encodeTrit zer) ≡ just zer
finite-coder-zero = refl

finite-coder-positive : decodeWord (encodeTrit pos) ≡ just pos
finite-coder-positive = refl

finite-coder-reserved-rejected : decodeWord word11 ≡ nothing
finite-coder-reserved-rejected = refl

constant-zero-mode-consistent :
  zeroModeEmbed (zeroModeKernel constantZeroMode) ≡
  zeroModeGenerator (zeroModeEmbed constantZeroMode)
constant-zero-mode-consistent = refl

constant-zero-mode-stable : zeroModeKernel constantZeroMode ≡ constantZeroMode
constant-zero-mode-stable = refl
