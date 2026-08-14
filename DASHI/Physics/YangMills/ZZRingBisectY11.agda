module DASHI.Physics.YangMills.ZZRingBisectY11 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

oneSixteenth : ℚ
oneSixteenth = + 1 / 16

idRaw : ∀ a b c →
  oneSixteenth * (a * a + (b * b + (c * c + (-(a + (b + c))) * (-(a + (b + c))))))
  ≡ oneSixteenth * (a * a + (b * b + (c * c + (-(a + (b + c))) * (-(a + (b + c))))))
idRaw = ℚRing.solve-∀
