module DASHI.Physics.YangMills.ZZRingBisectB6 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing

idRaw : ∀ a b c →
  (b - a) * (b - a) ≡ (b - a) * (b - a)
idRaw = ℚRing.solve-∀
