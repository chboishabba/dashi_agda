module DASHI.Physics.YangMills.ZZRingBisectY14 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

pivot2 : ℚ
pivot2 = + 13919 / 5516

idRaw : ∀ a b c →
  pivot2 * (c * c) ≡ pivot2 * (c * c)
idRaw = ℚRing.solve-∀
