module CICADA71 where

open import Agda.Builtin.Nat      using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_mod_)

------------------------------------------------------------------------
-- Bucket index in {0..70}
bucket71 : Nat → Nat
bucket71 n = n mod 71

------------------------------------------------------------------------
-- Periodicity statement: bucket71 (n + k*71) = bucket71 n
-- (prove via stdlib DivMod lemmas later, or keep as a postulate hook)

postulate
  bucket71-period : ∀ n k → bucket71 (n + k * 71) ≡ bucket71 n
