module DASHI.Physics.YangMills.ZZRingBisectY18 where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

pivot2 : ℚ
pivot2 = + 13919 / 5516

idRaw : pivot2 ≡ pivot2
idRaw = ℚRing.solve-∀
