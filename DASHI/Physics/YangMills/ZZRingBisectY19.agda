module DASHI.Physics.YangMills.ZZRingBisectY19 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

pivot2 : ℚ
pivot2 = + 139 / 55

idRaw : ∀ c →
  pivot2 * c ≡ pivot2 * c
idRaw = ℚRing.solve-∀
