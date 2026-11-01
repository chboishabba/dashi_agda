module DASHI.Physics.YangMills.ZZRingBisectA where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

sanity : ∀ a b c →
  (a + b + c) * (a + b + c) ≡ a * a + b * b + c * c + a * b + a * b + a * c + a * c + b * c + b * c
sanity = ℚRing.solve-∀
