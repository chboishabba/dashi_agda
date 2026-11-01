module DASHI.Arithmetic.CancellationPressureCore where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

-- Thin arithmetic surface for cancellation-pressure data.
-- This only fixes the carrier, step, and pressure seam.

record CancellationPressureCore : Set₁ where
  field
    Carrier : Set
    step : Carrier → Carrier
    cancellationPressure : Carrier → Nat
    pressure-step : ∀ x → cancellationPressure (step x) ≤ cancellationPressure x

open CancellationPressureCore public
