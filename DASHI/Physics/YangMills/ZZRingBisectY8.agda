module DASHI.Physics.YangMills.ZZRingBisectY8 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_; -_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing

idRaw : ∀ a b c →
  (b - a) * (b - a)
    + ((c - b) * (c - b)
    + ((-(a + (b + c))) - c) * ((-(a + (b + c))) - c))
  ≡ (b - a) * (b - a)
    + ((c - b) * (c - b)
    + ((-(a + (b + c))) - c) * ((-(a + (b + c))) - c))
idRaw = ℚRing.solve-∀
