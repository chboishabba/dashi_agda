module DASHI.Physics.YangMills.ZZRingBisectY1 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

idRaw : ∀ a b c →
  (a + b) * (a + b) ≡ a * a + (a * b + (a * b + b * b))
idRaw = ℚRing.solve-∀
