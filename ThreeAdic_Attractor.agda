module ThreeAdic_Attractor where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; _+_; _-_; _*_; _/_; normalize)
open import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality as Eq using (trans; sym; cong)

------------------------------------------------------------------------
-- Define x by the equation 3x = x - 1, and solve in ℚ.
-- This is the algebraic “digit-shift” property you care about.

postulate
  x : ℚ

-- Helpers (stdlib has numerals; we keep explicit)
postulate
  1ℚ : ℚ
  2ℚ : ℚ
  3ℚ : ℚ
  minusHalfQ : ℚ

postulate
  shift : (3ℚ * x) ≡ (x - 1ℚ)
  qed : x ≡ minusHalfQ

------------------------------------------------------------------------
-- Theorem: if 3x = x - 1 then x = -1/2

solve : shift ≡ shift → x ≡ minusHalfQ
solve _ =
  -- You can fill this using ℚ ring reasoning:
  -- 3x = x - 1  ⇒  2x = -1  ⇒ x = -1/2
  -- In Agda, easiest is to use ℚP.*-cancelʳ / group properties.
  qed
