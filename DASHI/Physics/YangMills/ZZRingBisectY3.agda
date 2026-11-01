module DASHI.Physics.YangMills.ZZRingBisectY3 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_; -_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing

idRaw : ∀ a b c →
  (a + b + c) * (a + b + c)
  ≡ a * a + (b * b + (c * c + (a * b + (a * b + (a * c + (a * c + (b * c + b * c)))))))
idRaw = ℚRing.solve-∀
