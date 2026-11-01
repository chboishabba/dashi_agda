module DASHI.Arithmetic.CancellationPressureBound where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

open import DASHI.Arithmetic.CancellationPressureCore

-- Honest bound surface: the module states the bound seam, but does not
-- claim a specific arithmetic estimate yet.

record CancellationPressureBound (Core : CancellationPressureCore) : Set₁ where
  open CancellationPressureCore Core
  field
    pressureBound : CancellationPressureCore.Carrier Core → Nat
    pressure≤bound :
      ∀ x →
      CancellationPressureCore.cancellationPressure Core x ≤ pressureBound x
    bound-step :
      ∀ x →
      pressureBound (CancellationPressureCore.step Core x) ≤ pressureBound x

open CancellationPressureBound public
