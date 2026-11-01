module DASHI.Physics.YangMills.ZZRingBisectY6 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

k : ℚ
k = + 1 / 16

idRaw : ∀ a b c →
  k * (a + (b + c))
  ≡ k * a + (k * b + k * c)
idRaw = ℚRing.solve-∀
