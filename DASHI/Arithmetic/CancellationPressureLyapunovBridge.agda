module DASHI.Arithmetic.CancellationPressureLyapunovBridge where

open import DASHI.Arithmetic.CancellationPressureCore
open import DASHI.Arithmetic.CancellationPressureMDL
open import DASHI.MDL.MDLLyapunov as MDL using (MDLLyapunov)

-- Bridge surface from arithmetic cancellation pressure into the repo's
-- Lyapunov interface. This is a target package, not a concrete proof.

record CancellationPressureLyapunovBridge (Core : CancellationPressureCore) : Set₁ where
  field
    mdlBridge : CancellationPressureMDL Core
    lyapunov :
      MDL.MDLLyapunov
        (CancellationPressureCore.step Core)
        (CancellationPressureMDL.mdlFunctional mdlBridge)

open CancellationPressureLyapunovBridge public
