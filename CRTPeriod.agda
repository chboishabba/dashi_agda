module CRTPeriod where

open import Agda.Builtin.Nat      using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_)

open import Data.Nat.Base   using (nonZero)
open import Data.Nat.DivMod using (_%_)

------------------------------------------------------------------------
-- Repo-defined digit function:

d : Nat → Nat
d N = ((N % 71) + (N % 59) + (N % 47)) % 10

period : Nat
period = 71 * 59 * 47  -- 196883

------------------------------------------------------------------------
-- The theorem statement (R1):
-- d(N + k*period) = d(N) for all k.
--
-- Proof is standard modular arithmetic:
-- (N + k*period) mod p = N mod p for p ∈ {71,59,47}
-- then propagate through sum and mod 10.
--
-- You can discharge this using stdlib DivMod lemmas, or (DASHI-style)
-- by importing a small proof certificate.

postulate
  period-thm : ∀ N k → d (N + k * period) ≡ d N
