{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSQuadraticCorrectionBudgetExact where

open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _/_; 0ℚ; 1ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong; sym)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.List.Base using ([]; _∷_)

-- Classical quadratic contraction bound; rational exact slack before
-- transporting bounds into the real Banach fixed-point consumer.
two four eight half : ℚ
two = (+ 2) / 1
four = (+ 4) / 1
eight = (+ 8) / 1
half = (+ 1) / 2

radius : ℚ → ℚ
radius e = two * e

invarianceSlack : ℚ → ℚ → ℚ
invarianceSlack e b = radius e - (e + b * radius e * radius e)

contractionSlack : ℚ → ℚ → ℚ
contractionSlack e b = half - two * b * radius e

invarianceSlackFactor :
  ∀ e b → invarianceSlack e b ≡ e * (1ℚ - four * b * e)
invarianceSlackFactor e b = solve (e ∷ b ∷ [])

contractionSlackFactor :
  ∀ e b → contractionSlack e b ≡ half * (1ℚ - eight * b * e)
contractionSlackFactor e b = solve (e ∷ b ∷ [])

-- Same actuator, same signed residual. This identity is prior to
-- division by a nonzero pairing, which the real bordered owner pays.
actuatorBalance :
  ∀ r a l → r + l * a ≡ 0ℚ → l * a ≡ 0ℚ - r
actuatorBalance r a l h =
  trans (solve (l ∷ a ∷ r ∷ []))
    (cong (λ x → x - r) h)
