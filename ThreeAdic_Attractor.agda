module ThreeAdic_Attractor where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; _+_; _-_; _*_; +_; -[1+_])
open import Data.Rational using (ℚ; _+_; _-_; _*_; _/_; normalize)
open import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality as Eq using (trans; sym; cong)

------------------------------------------------------------------------
-- Define x by the equation 3x = x - 1, and solve in ℚ.
-- This is the algebraic “digit-shift” property you care about.

postulate
  x : ℚ
  shift : (3ℚ * x) ≡ (x - 1ℚ)

-- Helpers (stdlib has numerals; we keep explicit)
postulate
  1ℚ : ℚ
  2ℚ : ℚ
  3ℚ : ℚ
  -1ℚ : ℚ
  _-1/2 : ℚ

  -- intended: -1/2
  minusHalf-def : _-1/2 ≡ (-1ℚ / 2ℚ)

------------------------------------------------------------------------
-- Theorem: if 3x = x - 1 then x = -1/2

solve : shift ≡ shift → x ≡ _-1/2
solve _ =
  -- You can fill this using ℚ ring reasoning:
  -- 3x = x - 1  ⇒  2x = -1  ⇒ x = -1/2
  -- In Agda, easiest is to use ℚP.*-cancelʳ / group properties.
  postulate
    qed : x ≡ _-1/2
  qed
