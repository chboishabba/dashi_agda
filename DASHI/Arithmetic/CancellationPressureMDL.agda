module DASHI.Arithmetic.CancellationPressureMDL where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_≤_)

open import DASHI.Arithmetic.CancellationPressureCore
open import DASHI.MDL.MDLLyapunov as MDL using (MDLFunctional)

-- Thin MDL seam for cancellation pressure.
-- It only asserts the intended matching between the pressure observable
-- and an MDL-style scalar; concrete instances can discharge it later.

record CancellationPressureMDL (Core : CancellationPressureCore) : Set₁ where
  open CancellationPressureCore Core
  field
    mdlFunctional : MDL.MDLFunctional (CancellationPressureCore.Carrier Core)
    cancellationPressure≈mdl :
      ∀ x →
      MDL.MDLFunctional.mdl mdlFunctional x ≡
      CancellationPressureCore.cancellationPressure Core x
    residual≤pressure :
      ∀ x →
      MDL.MDLFunctional.residual mdlFunctional x ≤
      CancellationPressureCore.cancellationPressure Core x

open CancellationPressureMDL public
