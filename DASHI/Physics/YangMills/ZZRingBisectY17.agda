module DASHI.Physics.YangMills.ZZRingBisectY17 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

idRaw : ∀ c →
  (+ 13919 / 5516) * c ≡ (+ 13919 / 5516) * c
idRaw = ℚRing.solve-∀
