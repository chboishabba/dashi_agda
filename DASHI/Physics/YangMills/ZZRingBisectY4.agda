module DASHI.Physics.YangMills.ZZRingBisectY4 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

idRaw : ∀ a b c →
  (+ 1 / 16) * (a + (b + c))
  ≡ (+ 1 / 16) * a + ((+ 1 / 16) * b + (+ 1 / 16) * c)
idRaw = ℚRing.solve-∀
