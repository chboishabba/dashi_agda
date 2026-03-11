module DASHI.Physics.Closure.MDLLyapunovCompatibility where

open import Data.Nat using (zero; z≤n)
open import MDL.Core.Core as OldMDL

-- Compatibility-only generic Lyapunov witness for interfaces that still
-- quantify over arbitrary transition systems.
abstract
  mdlLyapTrivial : ∀ {S : Set} (T : S → S) → OldMDL.Lyapunov T
  mdlLyapTrivial T =
    record
      { L = λ _ → zero
      ; descent = λ _ → z≤n
      }
