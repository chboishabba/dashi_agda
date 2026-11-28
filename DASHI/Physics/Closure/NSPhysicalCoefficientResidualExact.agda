{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSPhysicalCoefficientResidualExact where

open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _/_; 1ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.List.Base using ([]; _∷_)

-- Original Alpöge–Buckmaster Coercive.baseDensity, ad53419.
-- dd and dz retain the derivative norms of the two weight functions.
quarter : ℚ
quarter = (+ 1) / 4

density : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
density d z c w dd dz x2 xc x1 xo x0 =
  (d - c) * x2 * x2 + (1ℚ - d) * xc * xc
  + (quarter - z) * xo * xo
  + (z - dd - c * w) * x1 * x1 - dz * x0 * x0

densityDifference :
  ∀ d z c w dd dz d' z' c' w' dd' dz' x2 xc x1 xo x0 →
  density d z c w dd dz x2 xc x1 xo x0
    - density d' z' c' w' dd' dz' x2 xc x1 xo x0
  ≡ ((d - d') - (c - c')) * x2 * x2
    - (d - d') * xc * xc - (z - z') * xo * xo
    + ((z - z') - (dd - dd') - (c * w - c' * w')) * x1 * x1
    - (dz - dz') * x0 * x0
densityDifference d z c w dd dz d' z' c' w' dd' dz' x2 xc x1 xo x0 =
  solve (d ∷ z ∷ c ∷ w ∷ dd ∷ dz ∷ d' ∷ z' ∷ c' ∷ w' ∷ dd' ∷ dz'
    ∷ x2 ∷ xc ∷ x1 ∷ xo ∷ x0 ∷ [])

-- No deletion of the signed velocity channel, even on the mean mode.
splitMargin :
  ∀ d z c w dd dz a x2 xc x1 xo x0 →
  density d z c w dd dz x2 xc x1 xo x0
  ≡ a * (x2 * x2 + xc * xc + x1 * x1 + xo * xo)
    + (d - c - a) * x2 * x2 + (1ℚ - d - a) * xc * xc
    + (quarter - z - a) * xo * xo
    + (z - dd - c * w - a) * x1 * x1 - dz * x0 * x0
splitMargin d z c w dd dz a x2 xc x1 xo x0 =
  solve (d ∷ z ∷ c ∷ w ∷ dd ∷ dz ∷ a ∷ x2 ∷ xc ∷ x1 ∷ xo ∷ x0 ∷ [])

youngSquare :
  ∀ l x y → l * l * x * x + y * y - (l + l) * x * y
  ≡ (l * x - y) * (l * x - y)
youngSquare l x y = solve (l ∷ x ∷ y ∷ [])
