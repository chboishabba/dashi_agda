module DASHI.Physics.YangMills.ZZRingBisectY7 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing

idRaw : ∀ a b c →
  (b - a) * (b - a) + ((c - b) * (c - b) + c * c)
  ≡ (b * b - (a * b + a * b) + a * a) + ((c * c - (b * c + b * c) + b * b) + c * c)
idRaw = ℚRing.solve-∀
